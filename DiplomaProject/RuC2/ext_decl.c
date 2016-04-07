
#include "global_vars.h"

extern int  getnext();
extern int  nextch();
extern int  scaner();
extern void error(int e);

void mustbe(int what, int e)
{
    if (scaner() != what)
        error(e);
}

void totree(int op)
{
    tree[tc++] = op;
}

void totreef(int op)
{
    tree[tc++] = op;
    if ( ansttype == LFLOAT && ((op >= PLUSASS && op <= DIVASS) || (op >= PLUSASSAT && op <= DIVASSAT) ||
                                (op >= EQEQ && op <= UNMINUS)) )
        tree[tc-1] += 50;
}

int toidentab(int f)                 // f=0, если не ф-ция, f=1, если метка, f=funcnum, если описание ф-ции,
{                                    //  -1, если ф-ция-параметр, -2, если это описание типа
//    printf("\n repr %i rtab[repr] %i rtab[repr+1] %i rtab[repr+2] %i\n", repr, reprtab[repr], reprtab[repr+1], reprtab[repr+2]);
    int pred;
    lastid = id;
    if (reprtab[repr+1] == 0)                  // это может быть только MAIN
    {
        if (wasmain)
            error(more_than_1_main);
        wasmain = id;
    }
    pred = identab[id] = reprtab[repr+1];      // ссылка на описание с таким же представлением в предыдущем блоке
    if (pred)                                  // pred == 0 только для main, эту ссылку портить нельзя
        reprtab[repr+1] = id;                  // ссылка на текущее описание с этим представлением (это в reprtab)
    
    if (f != 1 && pred >= curid)               // один  и тот же идент м.б. переменной и меткой
        if (func_def == 3 ? 1 : identab[pred+1] > 0 ? 1 : func_def ==  1 ? 0 : 1)
            error(repeated_decl);              // только определение функции может иметь 2 описания, т.е. иметь предописание
    
    identab[id+1] = repr;                      // ссылка на представление
                                               // дальше тип или ссылка на modetab (для функций и структур)
    identab[id+2] = type;                      // тип -1 int, -2 char, -3 float, -5 []int, -6 []char, -7 []float,
                                               //                       -15 [][]int, -16 [][]char, -17 [][]float
                                               //-9 func int, -10 funcchar, -11 func float, -12 func void, 0-метка
                                               // если на 20 меньше, то это указатель на нужный тип
    if (f == 1)                                // если тип > 0, то это ссылка на modetab (для деклараторов и структур)
    {
        identab[id+2] = 0;                     // 0, если первым встретился goto, когда встретим метку, поставим 1
        identab[id+3] = 0;                     // при генерации кода когда встретим метку, поставим pc
    }
    else if (f == -2)
        identab[id+3] = 1;                     // это описание типа
    else if (f)
    {
            if (f < 0)  // сюда никогда не придем!
            {
                identab[id+3] = -(++displ);
                maxdispl = (displ > maxdispl) ? displ : maxdispl;
            }
            else                                                   // identtab[lastid+3] - номер функции, если < 0, то это функция-параметр
            {
                identab[id+3] = f;
                if (func_def == 2)
                    identab[lastid+1] *= -1;
            }
//        printf("toident id=%i lastid=%i func_def=%i identab[id]=%i\n", id, lastid, func_def, identab[id]);
    }
    else
    {
        identab[id+3] = displ + lg;            // смещение от l (полож) или от g (отриц), для меток - значение pc, для функций - номер

		displ += type > 0 && modetab[type] == MSTRUCT ? modetab[type + 3] * (lg) : lg; // для структур выделяем больше места

        if (lg < 0)
            maxdisplg = -displ;
        else
            maxdispl = (displ > maxdispl) ? displ : maxdispl;
    }
    id += 4;
    return lastid;
}

void binop(int op)
{
    int rtype = stackoperands[sopnd--];
    int ltype = stackoperands[sopnd];
    if (ltype < -20|| rtype < -20)
        error(operand_is_pointer);
    if ((ltype == LINT || ltype == LCHAR) && rtype == LFLOAT)
        totree(WIDEN1);
    if ((rtype == LINT || rtype == LCHAR) && ltype == LFLOAT)
        totree(WIDEN);
    if (ltype == LFLOAT || rtype == LFLOAT)
        ansttype = LFLOAT;
    totreef(op);
    if (op >= EQEQ && op <= LGE)
        ansttype = LINT;
    stackoperands[sopnd] = ansttype;
//    printf("binop sopnd=%i ltype=%i rtype=%i ansttype=%i\n", sopnd, ltype, rtype, ansttype);
    anst = VAL;
}

void expr();

void exprassn(int);

void toval(int t)
{
    if (anst == IDENT)
        tree[tc-2] = t;
    if (ansttype != ROWOFCHAR)
    {
        if (anst == ADDR && pntr > -20)
            totree(TAddrtoval);
        anst = VAL;
    }
}

void insertwiden()
{
    tc--;
    totree(WIDEN);
    totree(TExprend);
}

void applid()
{
    lastid = reprtab[repr+1];
    if (lastid == 1)
        error(ident_is_not_declared);
}

void primaryexpr()
{
    if (cur == NUMBER)
    {
        totree(TConst);                              // ansttype задается прямо в сканере
        totree((ansttype == LFLOAT) ? numr : num);   // LINT, LCHAR, FLOAT
        stackoperands[++sopnd] = ansttype;
//        printf("number sopnd=%i ansttype=%i\n", sopnd, ansttype);
        anst = NUMBER;
    }
    else if (cur == STRING)
    {
        int i = 0;
        totree(TString);
        do
            totree(lexstr[i]);
        while (lexstr[i++]);
        stackoperands[++sopnd] = ansttype;           // ROWOFCHAR
        anst = ADDR;
    }
    else if (cur == IDENT)
    {
        applid();
        totree(TIdent);
        totree(lastid);
        stackoperands[++sopnd] = ansttype  = identab[lastid+2];
//        printf("ident sopnd=%i ansttype=%i\n", sopnd,ansttype);
        anst = IDENT;
        anstdispl = identab[lastid+3];
//        printf("primary lastid= %i ansttype= %i\n", lastid, ansttype);
    }
    else if (cur == LEFTBR)
    {
        int oldsp = sp;
        scaner();
        expr();
        mustbe(RIGHTBR, wait_rightbr_in_primary);
        while (sp > oldsp)
            binop(stackop[--sp]);
    }
    else if (cur <= -25)            // стандартная функция
    {
        int func = cur;
        mustbe(LEFTBR, no_leftbr_in_stand_func);
        scaner();
        exprassn(1);
        if (func == GETDIGSENSOR || func == GETANSENSOR)
        {
            notrobot = 0;
            if (ansttype != LINT)
                error(param_setmotor_not_int);
            totree(400-func);
        }
        else if (func == ABS)
                if (ansttype == LINT)
                     totree(ABSIC);
                else if (ansttype == LFLOAT)
                         totree(ABSC);
                     else
                         error(bad_param_in_stand_func);
        else
        {
            if (ansttype == LINT)
            {
                ansttype = stackoperands[sopnd] = LFLOAT;
                totree(WIDEN);
            }
            totree(400-func);
        }
        mustbe(RIGHTBR, no_rightbr_in_stand_func);
    }
    else
        error(not_primary);
}

void index_check()
{
    if (ansttype != LINT && ansttype != LCHAR)
        error(index_must_be_int);
}

void postexpr()
{
    int lid, leftanst, leftansttype;
    primaryexpr();
    lid = lastid;
    
	while (next == LEFTSQBR || next == LEFTBR || next == DOT || next == ARROW || next == INC || next == DEC)
	{
		leftanst = anst;
		leftansttype = ansttype;
		if (next == LEFTSQBR)
		{
			int element_type, elem_type_len;
			if (modetab[ansttype] != MARRAY)
				error(slice_not_from_array);
			element_type = modetab[leftansttype + 2];
			elem_type_len = element_type > 0 && modetab[element_type] == MSTRUCT ? modetab[element_type + 3] : 1;
			scaner();
			scaner();
			if (leftanst == IDENT)
			{
				tree[tc - 2] = TSliceident;
				expr();
				index_check();
				totree(elem_type_len);
			}
			else
			{
				totree(TSlice);
				expr();
				index_check();					
				totree(elem_type_len);	// STRING
			}
			mustbe(RIGHTSQBR, no_rightsqbr_in_slice);

			stackoperands[--sopnd] = ansttype = element_type;
			anst = ADDR;
		}
		else if (next == LEFTBR)
		{
			int i, j, n, oldpntr = pntr;
			scaner();
			if (leftansttype < 0)
				error(call_not_from_function);
			if (identab[lid + 1] < 0)
				error(declarator_in_call);

			n = modetab[leftansttype + 2];

			totree(TCall1);
			totree(n);
			j = leftansttype + 3;
			for (i = 0; i<n; i++)
			{
				int mdj = modetab[j];  // это вид формального параметра, в ansttype будет вид фактического параметра
				scaner();
				if (mdj > 0)
				{
					int ld = reprtab[repr + 1];
					if (!(cur == IDENT && identab[ld + 2] == mdj))
						error(diff_formal_param_type_and_actual);
					totree(TIdenttoval);
					totree(ld);
					totree(TExprend);
				}
				else
				{
					pntr = mdj;
					exprassn(0);
					if ((mdj == LINT || mdj == LCHAR) && ansttype == LFLOAT)
						error(float_instead_int);
					if (mdj == LFLOAT && (ansttype == LINT || ansttype == LCHAR))
						insertwiden();

					//                 printf("ansttype= %i mdj= %i\n", ansttype, mdj);
					if (ansttype != mdj)
						error(diff_formal_param_type_and_actual);
					--sopnd;
					pntr = oldpntr;
				}
				if (i < n - 1 && scaner() != COMMA)
					error(no_comma_in_act_params);
				j++;
			}
			mustbe(RIGHTBR, wrong_number_of_params);
			totree(TCall2);
			totree(-lid);
			stackoperands[sopnd] = ansttype = modetab[leftansttype] + 8;   //  --?
			anst = VAL;
		}
		else if (next == DOT || next == ARROW)
		{
			int select_displ = 0, field_type;

			int needed_field_num = -1, num_of_fields, repr_field;
			op = scaner();
			mustbe(IDENT, after_dot_must_be_ident);

			if (modetab[ansttype] != MSTRUCT)
				error(get_field_not_from_struct);

			num_of_fields = modetab[ansttype + 4] / 2;

			for (int i = 0; i < num_of_fields; i++)
			{
				field_type = modetab[ansttype + 5 + i * 2];
				if (modetab[ansttype + 6 + i * 2] == repr)
				{
					needed_field_num = i;
					ansttype = field_type;
					break;
				}
				else
				{
					select_displ += modetab[field_type] == MSTRUCT ? modetab[field_type + 3] : 1; // прибавляем к суммарному смещению длину типа
				}
			}
			if (leftanst == IDENT)
			{
				tree[tc - 2] = TSelectId;
				totree(select_displ);
			}
			else
			{
				totree(TSelect);
				totree(select_displ);
			}
			anst = ADDR;
		}
		else if (ansttype > 0 && modetab[ansttype] == MFUNCTION)
			error(func_not_in_call);

		else if (next == INC || next == DEC)
		{
			if (ansttype != LINT && ansttype != LCHAR && ansttype != LFLOAT)
				error(wrong_operand);
			if (anst != IDENT && anst != ADDR)
				error(unassignable_inc);
			int op = (next == INC) ? POSTINC : POSTDEC;
			if (anst == ADDR)
				op += 4;
			scaner();
			totreef(op);
			if (anst == IDENT)
				totree(-lid);
			anst = VAL;
		}
	}
}

void unarexpr()
{
    if (cur == LNOT || cur == LOGNOT || cur == LPLUS || cur == LMINUS || cur == LAND || cur == LMULT)
    {
        int op  = cur;
        scaner();
        if (op == LAND || op == LMULT)
        {
            postexpr();
            if (op == LAND)
            {
                if (anst != IDENT && anst != ADDR)
                    error(wrong_addr);
                if (anst == IDENT)
                    toval(TIdenttoaddr);
                ansttype -= 20;
            }
            else
            {
                toval(TIdenttoval);
                if (ansttype > -20)
                    error(aster_not_for_pointer);
                totree(LAT);
                ansttype += 20;
            }
        }
        else
        {
            unarexpr();
            if ((op == LNOT || op == LOGNOT) && ansttype == LFLOAT)
                error(int_op_for_float);
            else if (op == LMINUS)
                totreef(UNMINUS);
            else if (op == LPLUS)
                ;
            else
                totree(op);
            stackoperands[sopnd] = ansttype;
            anst = VAL;
        }
    }
    else if (cur == INC || cur == DEC)
    {
        int op = cur;
        scaner();
        postexpr();
        if  (anst != IDENT && anst != ADDR)
            error(unassignable_inc);
        if (anst == ADDR)
            op += 4;
        totreef(op);
        if (anst == IDENT)
            totree(-lastid);
        anst = VAL;
    }
    else
        postexpr();
}

void exprinbrkts()
{
    mustbe(LEFTBR, cond_must_be_in_brkts);
    scaner();
    expr();
    mustbe(RIGHTBR, cond_must_be_in_brkts);
}

int prio(int op)   // возвращает 0, если не операция
{
    return  op == LOGOR ? 1 : op == LOGAND ? 2 : op == LOR ? 3 : op == LEXOR ? 4 : op == LAND ? 5 :
    op == EQEQ ? 6 : op == NOTEQ ? 6 :
    op == LLT  ? 7 : op == LGT ?   7 : op  == LLE ? 7 : op == LGE ? 7 :
    op == LSHL ? 8 : op == LSHR ? 8 : op == LPLUS ? 9 : op == LMINUS ? 9 :
	op == LMULT ? 10 : op == LDIV ? 10 : op == LREM ? 10 : op == DOT ? 11 : 0;
}

void subexpr()
{
    int p, oldsp = sp, wasop = 0;
    while ((p = prio(next)))
    {
        wasop = 1;
        toval(TIdenttoval);
        while (sp > oldsp && stack[sp-1] >= p)
            binop(stackop[--sp]);
        
        stack[sp] = p;
        stackop[sp++] = next;
        scaner();
        scaner();
        unarexpr();
    }
    if (wasop)
        toval(TIdenttoval);
    while (sp > oldsp)
        binop(stackop[--sp]);
}

int opassn()
{
    op = next;
    return  next == ASS || next == MULTASS || next == DIVASS ||next == REMASS || next == PLUSASS || next == MINUSASS ||
    next == SHLASS || next == SHRASS || next == ANDASS || next == EXORASS || next == ORASS;
}

void condexpr()
{
    int globtype = 0, adif = 0, r, oldpntr = pntr;
    subexpr();                   // logORexpr();
    if (next == QUEST)
    {
        while (next == QUEST)
        {
            int thenref, elseref;
            pntr = 0;
            toval(TIdenttoval);
            if (ansttype == LFLOAT)
                error(float_in_condition);
            totree(TCondexpr);
            thenref = tc++;
            elseref = tc++;
            scaner();
            scaner();
            sopnd--;
            tree[thenref] = tc;
            pntr = oldpntr;
            expr();                  // then
            if (!globtype)
                globtype = ansttype;
            sopnd--;
            if (ansttype == LFLOAT)
                globtype = LFLOAT;
            else
            {
                tree[tc] = adif;
                adif = tc++;
            }
            mustbe(COLON, no_colon_in_cond_expr);
            scaner();
            tree[elseref] = tc;
            unarexpr();
            subexpr();   // logORexpr();        else or elif
        }
        toval(TIdenttoval);
        totree(TExprend);
        if (ansttype == LFLOAT)
            globtype = LFLOAT;
        else
        {
            tree[tc] = adif;
            adif = tc++;
        }
        do
        {
            r = tree[adif];
            tree[adif] = TExprend;
            tree[adif-1] = globtype == LFLOAT ? WIDEN : NOP;
            adif = r;
        }
        while (adif);
        
            stackoperands[sopnd] = globtype;
//        printf("cond1 sopnd=%i globtype=%i\n", sopnd, globtype);
    }
    else
    {
        toval(TIdenttoval);
        stackoperands[sopnd] = ansttype;
//    printf("cond2  sopnd=%i ansttype=%i\n", sopnd, ansttype);
    }
}

void exprassnvoid()
{
    int t = tree[tc-2] < 0 ? tc-3 : tc-2;
    if ((tree[t] >= ASS && tree[t] <= DIVASSAT)       || (tree[t] >= POSTINC && tree[t] <= DECAT) ||
        (tree[t] >= PLUSASSR && tree[t] <= DIVASSATR) || (tree[t] >= POSTINCR && tree[t] <= DECATR))
         tree[t] += 200;
    --sopnd;
}

void exprassn(int level)
{
    int opp = 0, leftanst, lid, oldpntr;
    unarexpr();
    leftanst = anst;
    lid = lastid;
    while (opassn())
    {
        oldpntr = pntr;
        pntr = ansttype;
        scaner();
        scaner();
        opp = op;
        exprassn(level + 1);
        pntr = oldpntr;
    }
    if (opp)
    {
        int rtype = stackoperands[sopnd--];
        int ltype = stackoperands[sopnd--];
        if (ltype < -20 && ltype != rtype && ltype != rtype - 20)
                error(wrong_pnt_assn);
        if ((ltype == LINT || ltype == LCHAR) && rtype == LFLOAT)
            error(assmnt_float_to_int);
        if ((rtype == LINT ||rtype == LCHAR) && ltype == LFLOAT)
            totree(WIDEN);
        if (ltype == LFLOAT || rtype == LFLOAT)
            ansttype = LFLOAT;
        stackoperands[sopnd] = ansttype;
        if (leftanst == ADDR)
            opp += 11;
        totreef(opp);
        if (leftanst ==IDENT)
            totree(-lid);
    }
    else
    {
        condexpr();    // condexpr учитывает тот факт, что начало выражения в виде unarexpr уже выкушано
    }
    if (level == 0)
        totree(TExprend);
}

void expr()
{
    int oldpntr = pntr;
    pntr = 0;
    exprassn(0);
    while (next == COMMA)
    {
        exprassnvoid();
        sopnd--;
        scaner();
        scaner();
        exprassn(0);
    }
    pntr = oldpntr;
}

int arrinit(int decl_type)
{
    int ni = 0;
    scaner();
    mustbe(BEGIN, arr_init_must_start_from_BEGIN);
    while (next != END)
    {
        ni++;
        scaner();
        pntr = decl_type;
        exprassn(0);
        sopnd--;
        if ((decl_type == LINT || decl_type == LCHAR) && ansttype == LFLOAT)
            error(init_int_by_float);
        if (decl_type == LFLOAT && ansttype != LFLOAT)
            insertwiden();
        if (next == COMMA)
            scaner();
        else if (next != END)
            error(no_comma_in_init_list);
    }
    scaner();
    return ni;

}

void decl_id()
{
	int decl_type = type;
    int oldid = toidentab(0);
    int initref, n, ni;     // n - размерность (0-скаляр), д.б. столько выражений-границ, инициализатор начинается с L  
    totree(TDeclid);
    totree(oldid);
    initref = tc++;
    tree[n = tc++] = 0;
    if (next == ASS)
    {
        scaner();
        scaner();
        tree[initref] = tc;
        pntr = type;
        exprassn(0);
        sopnd--;
        if ((decl_type == LINT || decl_type == LCHAR) && ansttype == LFLOAT)
            error(init_int_by_float);
        if (decl_type == LFLOAT && ansttype != LFLOAT)
            insertwiden();
    }
    else if (next == LEFTSQBR)
    {
		while (next == LEFTSQBR)
		{
			scaner();
			scaner();
			tree[n]++;
			identab[oldid + 2] =  get_array_type(identab[oldid + 2]);
			pntr = LINT;
			unarexpr();
			condexpr();
			totree(TExprend);
			sopnd--;
			mustbe(RIGHTSQBR, wait_right_sq_br);
			if (next == ASS)
			{
				tree[initref] = tc;
				totree(TInit);
				ni = tc++;
				tree[ni] = arrinit(decl_type);
			}
		}
    }
}

void block(int b);
 // если b=1, то это просто блок, b=-1 - блок в switch, иначе (b=0) - это блок функции

void statement()
{
    int flagsemicol = 1, oldwasdefault = wasdefault, oldinswitch = inswitch;
    wasdefault = 0;
    scaner();
    if ((cur == LINT || cur == LCHAR || cur == LFLOAT || cur == LVOID || cur == LSTRUCT) && blockflag)
        error(decl_after_strmt);
    if (cur == BEGIN)
    {
        flagsemicol = 0;
        block(1);
    }
    else if (cur == SEMICOLON)
        flagsemicol = 0;
    else if (cur == IDENT && next == COLON)
    {
        int id, i, flag = 1;
        flagsemicol = 0;
        totree(TLabel);
        for (i=0; flag && i < pgotost-1; i+=2)
            flag = identab[ gotost[i]+1] != repr;
        if (flag)
        {
            totree(id = toidentab(1));
            gotost[pgotost++] = id;              // это определение метки, если она встретилась до переходов на нее
            gotost[pgotost++] = -line;
        }
        else
        {
            id = gotost[i-2];
            repr = identab[id+1];
            if (gotost[i-1] < 0)
                error(repeated_label);
            totree(id);
        }
        identab[id+2] = 1;

        scaner();
        statement();
    }
    else
    {
        blockflag = 1;
        switch (cur)
        {
            case PRINT:
            {
                exprinbrkts();
                totree(TPrint);
                totree(ansttype);
                if (ansttype < -20)
                    error( pointer_in_print);
                sopnd --;
            }
                break;
            case PRINTID:
            {
                mustbe(LEFTBR, no_leftbr_in_printid);
                mustbe(IDENT, no_ident_in_printid);
                lastid = reprtab[repr+1];
                if (lastid == 1)
                    error(ident_is_not_declared);
                totree(TPrintid);
                totree(lastid);
                mustbe(RIGHTBR, no_rightbr_in_printid);
            }
                break;
        case GETID:
            {
                mustbe(LEFTBR, no_leftbr_in_printid);
                mustbe(IDENT, no_ident_in_printid);
                lastid = reprtab[repr+1];
                if (lastid == 1)
                    error(ident_is_not_declared);
                totree(TGetid);
                totree(lastid);
                mustbe(RIGHTBR, no_rightbr_in_printid);
                break;
            }
            case SETMOTOR:
            {
                notrobot = 0;
                mustbe(LEFTBR, no_leftbr_in_setmotor);
                scaner();
                exprassn(0);
                if (ansttype != LINT)
                    error(param_setmotor_not_int);
                mustbe(COMMA, no_comma_in_setmotor);
                scaner();
                exprassn(0);
                if (ansttype != LINT)
                    error(param_setmotor_not_int);
                sopnd -= 2;
                totree(SETMOTOR);
                mustbe(RIGHTBR, no_rightbr_in_setmotor);
                break;
            }
            case SLEEP:
            {
                notrobot = 0;
                mustbe(LEFTBR, no_leftbr_in_sleep);
                scaner();
                exprassn(0);
                if (ansttype != LINT)
                    error(param_setmotor_not_int);
                sopnd --;
                totree(SLEEP);
                mustbe(RIGHTBR, no_rightbr_in_sleep);
                break;
            }
            case LBREAK:
            {
                if (! (inloop || inswitch))
                    error(break_not_in_loop_or_switch);
                totree(TBreak);
            }
                break;
            case LCASE:
            {
                if (! inswitch)
                    error(case_or_default_not_in_switch);
                if (wasdefault)
                    error(case_after_default);
                scaner();
                flagsemicol = 0;
                pntr = LINT;
                unarexpr();
                condexpr();
                totree(TExprend);
                if (ansttype == LFLOAT)
                    error(float_in_switch);
                sopnd--;
                if (next != COLON)
                    error(no_colon_in_case);
                scaner();
                totree(TCase);
                totree(num);
                statement();
            }
                break;
            case LCONTINUE:
            {
                if (! inloop)
                    error(continue_not_in_loop);
                totree(TContinue);
            }
                break;
            case LDEFAULT:
            {
                if (! inswitch)
                    error(case_or_default_not_in_switch);
                if (next != COLON)
                    error(no_colon_in_case);
                wasdefault = 1;
                totree(TDefault);
                scaner();
                statement();
            }
                break;
            case LDO:
            {
                inloop = 1;
                int condref;
                totree(TDo);
                condref = tc++;
                statement();
                if (next == LWHILE)
                {
                    scaner();
                    tree[condref] = tc;
                    exprinbrkts();
                    sopnd--;
                }
                else
                    error(wait_while_in_do_stmt);
                inloop = 0;
            }
                break;
            case LFOR:
            {
                int fromref,condref, incrref, stmtref;
                mustbe(LEFTBR, no_leftbr_in_for);
                inloop = 1;
                totree(TFor);
                fromref = tc++;
                condref = tc++;
                incrref = tc++;
                stmtref = tc++;
                if (scaner() == SEMICOLON)             // init
                    tree[fromref] = 0;
                else
                {
                    tree[fromref] = tc;
                    expr();
                    exprassnvoid();
                    mustbe(SEMICOLON, no_semicolon_in_for);
                }
                if (scaner() == SEMICOLON)             // cond
                    tree[condref] = 0;
                else
                {
                    tree[condref] = tc;
                    pntr = LINT;
                    expr();
                    sopnd --;
                    mustbe(SEMICOLON, no_semicolon_in_for);
                    sopnd--;
                }
                if (scaner() == RIGHTBR)              // incr
                    tree[incrref] = 0;
                else
                {
                    tree[incrref] = tc;
                    expr();
                    exprassnvoid();
                    mustbe(RIGHTBR, no_rightbr_in_for);
                }
                flagsemicol = 0;
                tree[stmtref] = tc;
                statement();
                inloop = 0;
            }
                break;
            case LGOTO:
            {
                int i, flag = 1;
                mustbe(IDENT, no_ident_after_goto);
                totree(TGoto);
                for (i=0; flag && i < pgotost-1; i+=2)
                    flag = identab[ gotost[i]+1] != repr;
                if (flag)
                {                                 // первый раз встретился переход на метку, которой не было, в этом случае
                    totree(-toidentab(1));        // ссылка на identtab, стоящая после TGoto, будет отрицательной
                    gotost[pgotost++] = lastid;
                }
                else
                {
                    int id = gotost[i-2];
                    if (gotost[id+1] < 0)          // метка уже была
                    {
                        totree(id);
                        break;
                    }
                    totree(gotost[pgotost++] = id);
                }
                gotost[pgotost++] = line;
            }
                break;
            case LIF:
            {
                int thenref, elseref;
                totree(TIf);
                thenref = tc++;
                elseref = tc++;
                flagsemicol = 0;
                exprinbrkts();
                tree[thenref] = tc;
                sopnd--;
                statement();
                if (next == LELSE)
                {
                    scaner();
                    tree[elseref] = tc;
                    statement();
                }
                else
                    tree[elseref] = 0;
            }
                break;
            case LRETURN:
            {
                int ftype = modetab[functype+1];
                wasret = 1;
                if (next == SEMICOLON)
                {
                    if (ftype != FUNCVOID)
                        error(no_ret_in_func);
                    totree(TReturn);
                }
                else
                {
                    scaner();
                    if (ftype == FUNCVOID)
                        error(notvoidret_in_void_func);
                    totree(TReturnval);
                    ftype += 8;
                    expr();
                    sopnd--;
                    if (ftype ==LFLOAT && ansttype == LINT)
                        totree(WIDEN);
                    else if (ftype != ansttype)
                        error(bad_type_in_ret);
                }
            }
                break;
            case LSWITCH:
            {
                flagsemicol = 0;
                totree(TSwitch);
                exprinbrkts();
                if (ansttype != LCHAR && ansttype != LINT)
                    error(float_in_switch);
                sopnd--;
                scaner();
                block(-1);
                wasdefault = 0;
                inswitch = oldinswitch;
            }
                break;
            case LWHILE:
            {
                int doref;
                inloop = 1;
                totree(TWhile);
                doref = tc++;
                flagsemicol = 0;
                exprinbrkts();
                sopnd--;
                tree[doref] = tc;
                statement();
                inloop = 0;
            }
                break;
            default:
                expr();
                exprassnvoid();
        }
    }
    if (flagsemicol && scaner() != SEMICOLON)
        error(no_semicolon_after_stmt);
    wasdefault = oldwasdefault;
    inswitch = oldinswitch;
}

void idorpnt(int e)
{
    point = 0;
    if (next == LMULT)
    {
        scaner();
        point = -20;
    }
    mustbe(IDENT, e);
}

// проверяет, имеется ли в modetab только что внесенный тип.
// если да, то возвращает ссылку на старую запись, иначе - на новую.
int check_duplicates()
{
	int old = modetab[startmode];
	while (old)
	{
		if (modeeq(startmode + 1, old + 1))
			break;
		else
			old = modetab[old];
	}

	if (old)
	{
		md = startmode + 1;
		return old + 1;
	}
	else
	{
		modetab[md] = startmode;
		startmode = md++;
		return modetab[startmode] + 1;
	}
}

int get_type_len(int t)
{
	int len = 0, i;
	if (t < 0 || modetab[t] != MSTRUCT)
		return 1; 
	
	int fields_count = modetab[t + 4] / 2;
	for (i = 0; i < fields_count; i++)
	{
		len += get_type_len(modetab[t + 5 + i * 2]);
	}
	return len;
}

int get_pointer_type(int t)
{
	int pointer_ref = modetab[t + 2];
	if (modetab[pointer_ref] == MPOINT)
		return pointer_ref;

	int result_type = md;
	modetab[md++] = MPOINT;
	modetab[md++] = 0; // ссылка на массив
	modetab[md++] = 0; // ссылка на указатель
	modetab[md++] = t; // ссылка на элемент
	return modetab[t + 2] = check_duplicates();
}

int get_array_type(int t)
{
	int array_ref = modetab[t + 1], res;
	if (modetab[array_ref] == MARRAY)
		return array_ref;

	int result_type = md;
	modetab[md++] = MARRAY;
	modetab[md++] = 0; // ссылка на массив
	modetab[md++] = t; // ссылка на элемент
	return modetab[t + 1] = check_duplicates();
}

int struct_decl_list()
{
	int field_count = 0, oldmd, i, t;
	int loc_modetab[100], locmd = 5;
	loc_modetab[0] = MSTRUCT; // У структуры тут 1.
	loc_modetab[1] = loc_modetab[2] = 0; //Ссылка на массив этого типа и на указатель этого типа.

	scaner();
	while (next != END)
	{
		t = gettype();
		do
		{
			idorpnt(wait_ident_after_comma_in_decl);
			loc_modetab[locmd++] = t;
			loc_modetab[locmd++] = repr;
			field_count++;
		} while (scaner() == COMMA);
	    
		if (cur != SEMICOLON)
			error(def_must_end_with_semicomma);
	}
	scaner();

	loc_modetab[3] = 0;
	loc_modetab[4] = field_count * 2;

	oldmd = md;
	for (i = 0; i < locmd; i++)
		modetab[md++] = loc_modetab[i];

	modetab[oldmd + 3] = get_type_len(oldmd);

	return check_duplicates();
}

// gettype() выедает тип вместе со *(в случае указателей)
// при этом, если такого типа нет в modetab, тип туда заносится;
// возвращает отрицательное число(базовый тип) или положительное (ссылка на modetab)
int gettype()
{
	int result_type;
    if((type = scaner()) == LINT || type == LFLOAT || type == LCHAR || type == LVOID)
		result_type =  type;
    else if (type == LSTRUCT)
    {
        if (next == BEGIN)             // struct {
			result_type = struct_decl_list();
        else if (next == IDENT)
        {
			int l = reprtab[repr + 1];
			scaner();
            if (next == BEGIN)         // struct key {
            {
                int lid;
				wasstructdef = 1;
                toidentab(-2);
                lid = lastid;
				result_type = identab[lid + 2] = struct_decl_list();
            }
            else
            {                           // struct key
				if (l == 1)
					error(ident_is_not_declared);
				result_type = identab[l + 2];
            }
        }
		else 
			error(wrong_struct);
    }
	while (next == LMULT)
	{
		scaner();
		result_type = get_pointer_type(result_type);
	}
	return result_type;
}

void block(int b)
// если b=1, то это просто блок, b=-1 - блок в switch, иначе (b=0) - это блок функции

{
    int oldinswitch = inswitch, t;
    int notended = 1, i, olddispl, oldlg = lg, firstdecl;
    inswitch = b < 0;
    totree(TBegin);
    if (b)
    {
        olddispl = displ;
        curid = id;
    }
    blockflag = 0;
    
	while (next == LINT || next == LCHAR || next == LFLOAT || next == LSTRUCT)
    {
		firstdecl = gettype();
		if (next == SEMICOLON && wasstructdef)
		{
			scaner();
			continue;
		}
        int repeat = 1;
        idorpnt(after_type_must_be_ident);
        do
        {
            type = firstdecl + point;
            
            decl_id();
            
            if (next == COMMA)
            {
                scaner();
                idorpnt(wait_ident_after_comma_in_decl);
            }
            else if (next == SEMICOLON)
                 {
                     scaner();
                     repeat = 0;
                 }
                 else
                     error(def_must_end_with_semicomma);
        }
        while (repeat);
    }
    
    // кончились описания, пошли операторы до }

    do
    {
        if (next == END)
        {
            scaner();
            notended = 0;
        }
        else
            statement();
    }
    while (notended);
    if (b)
    {
        for (i=id-4; i>=curid; i-=4)
            reprtab[ identab[i+1]+1] = identab[i];
            displ = olddispl;
    }
    inswitch = oldinswitch;
    lg = oldlg;
    totree(TEnd);
}

int modeeq(int first_mode, int second_mode)
{
	int n, i, flag = 1, mode;
	if (modetab[first_mode] != modetab[second_mode])
		return 0;

	mode = modetab[first_mode];
	n = mode == MARRAY    ? 2 :
		mode == MPOINT    ? 3 :
		mode == MSTRUCT   ? 4 + modetab[first_mode + 4] : 
		mode == MFUNCTION ? 2 + modetab[first_mode + 2] : 0;

    for (i=0; i<n && flag ; i++)
		flag = modetab[first_mode + i + 1] == modetab[second_mode + i + 1];

    return flag;
}

void function_definition()
{
    int fn = identab[lastid+3], i, pred, oldrepr = repr, ftype, n, fid = lastid;
    pgotost = 0;
    functype = identab[lastid+2];
    ftype = modetab[functype+1];
    n = modetab[functype+2];
    wasret = 0;
    displ = 2;
    maxdispl =3;
    lg = 1;
    if ((pred = identab[lastid]) > 1)            // был прототип
        if (functype != identab[pred+2])
            error(decl_and_def_have_diff_type);
    curid = id;
    for (i=0; i < n; i++)
    {
        type = modetab[functype+i+3];
        repr = functions[fn+i+1];
        if (repr > 0)
            toidentab(0);
        else
        {
            repr = -repr;
            toidentab(-1);
        }
    }
    functions[fn]= tc;
    totree(TFuncdef);
    totree(fid);
    pred = tc++;
    repr = oldrepr;
    block(0);
    if (ftype == FUNCVOID && tree[tc-1] != TReturn)
    {
        tc--;
        totree(TReturn);
        totree(TEnd);
    }
    if ((ftype == FUNCINT || ftype == FUNCCHAR || ftype == FUNCFLOAT) && !wasret)
        error(no_ret_in_func);
    for (i=id-4; i>=curid; i-=4)
        reprtab[ identab[i+1]+1] = identab[i];
    
    for (i=0; i < pgotost-1; i+=2)
    {
        repr = identab[gotost[i]+1];
        hash = gotost[i+1];
        if (hash <0 )
            hash = - hash;
        if ( !identab[gotost[i]+2])
            error(label_not_declared);
    }
    curid = 2;                                 // все функции описываются на одном уровне
    tree[pred] = maxdispl + 1;
    lg = -1;
}

int func_declarator(int level, int func_d, int firstdecl)
{
    // на 1 уровне это может быть определением функции или предописанием, на остальных уровнях - только декларатором (без идентов)
    
    int loc_modetab[100], locmd = 0, numpar = 0, ident, maybe_fun, repeat = 1, i, wastype = 0, old;
    
	loc_modetab[0] = MFUNCTION;
    loc_modetab[1] = firstdecl;
    loc_modetab[2] = 0;
    locmd = 3;
    
    while (repeat)
    {
        if ((type = cur) == LINT || cur == LCHAR || cur == LFLOAT)
        {
            maybe_fun = 0;    // м.б. параметр-ф-ция? 0 - ничего не было, 1 - была *, 2 - была [
            ident = 0;        // = 0 - не было идента, 1 - был статический идент, 2 - был идент-параметр-функция
            wastype = 1;
            point = 0;
            if (next == LMULT)
            {
                scaner();
                type -= 20;
                maybe_fun = 1;
            }
            if (level)
            {
                if (next == IDENT)
                {
                    scaner();
                    ident = 1;
                    functions[funcnum++] = repr;
                }
            }
            else if (next == IDENT)
                error(ident_in_declarator);
            if (next == LEFTSQBR)
            {
                scaner();
                maybe_fun = 2;
                if (type < -20)
                    error(aster_with_row);
                mustbe(RIGHTSQBR, wait_right_sq_br);
                if (next == LEFTSQBR)
                {
                    scaner();
                    mustbe(RIGHTSQBR, wait_right_sq_br);
                    type -= 14;
                }
                else
                    type -= 4;
            }
        }
        else if ((type = cur) == LVOID)
        {
            wastype = 1;
            if (next != LEFTBR)
                error(par_type_void_with_nofun);
        }
        if (wastype)
        {
            numpar++;
            loc_modetab[locmd++] = type;
        
            if (next == LEFTBR)
            {
                scaner();
                mustbe(LMULT, wrong_fun_as_param);
                if (next == IDENT)
                {
                    if (level)
                    {
                        scaner();
                        if (ident == 0)
                            ident = 2;
                        else
                            error(two_idents_for_1_declarer);
                        functions[funcnum++] = -repr;
                    }
                    else
                        error(ident_in_declarator);
                }
                mustbe(RIGHTBR, no_right_br_in_paramfun);
                mustbe(LEFTBR, wrong_fun_as_param);
                scaner();
                if (maybe_fun == 1)
                    error(aster_before_func);
                else if (maybe_fun == 2)
                    error(array_before_func);

                old = func_def;
                loc_modetab[locmd-1] = func_declarator(0, 2, type-8);
                func_def = old;
            }
//            printf("level=%i ident1=%i func_d=%i loc_m=%i\n", level, ident, func_d, loc_modetab[locmd-2]);

            if (func_d == 3)
                func_d = ident > 0 ? 1 : 2;
            else if (func_d == 2 && ident > 0)
                error(wait_declarator);
            else if (func_d == 1 && ident == 0)
                error(wait_definition);
            
            if (scaner() == COMMA)
            {
                scaner();
            }
            else
                if (cur == RIGHTBR)
                    repeat = 0;
        }
        else if (cur == RIGHTBR)
        {
            repeat = 0;
            func_d = 0;
        }
             else
                 error(wrong_param_list);
    }
    func_def = func_d;
    locmd = md;
    loc_modetab[2] = numpar;

    for (i=0; i < numpar+3; i++)
        modetab[md++] = loc_modetab[i];

	return check_duplicates();
}

void ext_decl()
{
    do            // top level описания переменных и функций до конца файла
    {
        int repeat = 1, funrepr, first = 1, t;
        wasstructdef = 0;
        type = gettype();
		if (wasstructdef && next == SEMICOLON)
		{
			scaner();
			goto ex;
		}
            
        func_def = 3;   // func_def = 0 - (), 1 - определение функции, 2 - это предописание, 3 - не знаем или вообще не функция

		if (type)
            idorpnt(after_type_must_be_ident);
        else
        {
            type = LINT;
            point = 0;
            if (cur == LMULT)
            {
                scaner();
                point -= 20;
            }
        }
        firstdecl = type;
        type += point;
        do                       // описываемые объекты через ',' определение функции может быть только одно, никаких ','
        {
            if (cur != IDENT)
                error(decl_must_start_from_ident_or_decl);
            
            if (firstdecl  < -20 && next == LEFTBR)
                error(aster_before_func);
            
            if (next == LEFTBR)                // определение или предописание функции
            {
                int oldfuncnum = funcnum++;
                funrepr = repr;
                scaner();
                scaner();
                type = func_declarator(first, 3, firstdecl-8);  // выкушает все параметры до ) включительно
                if (next == BEGIN)
                {
                    if (func_def == 0)
                        func_def = 1;
                }
                else if (func_def == 0)
                    func_def = 2;
                                          // теперь я точно знаю, это определение ф-ции или предописание (func_def=1 или 2)
                repr =funrepr;
                toidentab(oldfuncnum);
                
                if (next == BEGIN)
                {
                    scaner();
                    if (func_def == 2)
                        error(func_decl_req_params);
                    
                    function_definition();
                    goto ex;
                }
                else
                {
                    if (func_def == 1)
                    error(function_has_no_body);
                }
            }
            else
                if (firstdecl == LVOID)
                    error(only_functions_may_have_type_VOID);
            
// описания идентов-не-функций

            if (func_def == 3)
                decl_id();
            if (next == COMMA)
            {
                scaner();
                first = 0;
                idorpnt(wait_ident_after_comma_in_decl);
                type = firstdecl + point;
            }
            else if (next == SEMICOLON)
                 {
                     scaner();
                     repeat = 0;
                 }
                 else
                    error(def_must_end_with_semicomma);
        }
        while (repeat);
    ex: ;
    }
    while (next != LEOF);
    
    if (wasmain == 0)
        error(no_main_in_program);
}
