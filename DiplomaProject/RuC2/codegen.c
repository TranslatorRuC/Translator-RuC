//
//  codegen.c
//
//  Created by Andrey Terekhov on 3/10/15.
//  Copyright (c) 2015 Andrey Terekhov. All rights reserved.
//
#include "global_vars.h"

extern void error(int err);

void tocode(int c)
{
//    printf("pc %i) %i\n", pc, c);
    mem[pc++] = c;
}

void adbreakend()
{
    while (adbreak)
    {
        int r = mem[adbreak];
        mem[adbreak] = pc;
        adbreak = r;
    }
}

void adcontend()
{
    while (adcont)
    {
        int r = mem[adcont];
        mem[adcont] = pc;
        adcont = r;
    }
}


void Expr_gen(int adfi)
{
    int flagprim = 1, c;
    while (flagprim)
    {
        switch (tree[tc])
        {
            case TIdent:
            {
                tc++;
                lastid = tree[tc++];
                anstdispl = identab[lastid+3];
            }
                break;
                
            case TIdenttoval:
            {
                tc++;
                lastid = tree[tc++];
                anstdispl = identab[lastid+3];
                if (identab[lastid+2] > 0)
                {
                    if (anstdispl > 0)
                    {
                        tocode(LI);
                        tocode(anstdispl);
                    }
                    else
                    {
                        tocode(LOAD);
                        tocode(-anstdispl);
                    }
                }
                else
                {
                tocode(LOAD);
                tocode(anstdispl);
                }
            }
                break;

            case TAddrtoval:
            {
                tc++;
                tocode(LAT);
            }
                break;
                
            case TConst:
            {
                tc++;
                tocode(LI);
                tocode(tree[tc++]);
            }
                break;
                
            case TString:
            {
                tc++;
                int n = -1, res;
                tocode(LI);
                tocode(res = pc+4);
                tocode(B);
                pc += 2;
                do
                    n++, tocode(tree[tc]);
                while (tree[tc++]);
                
                mem[res-1] = n;
                mem[res-2] = pc;
            }
                break;
                
            case TSliceident:
            {
                int displ = identab[tree[++tc] + 3];
                tc++;
                tocode(LOAD);
                tocode(displ);
                Expr_gen(0);
                tocode(SLICE);
            }
                break;
                
            case TSlice:
            {
                tc++;
                tocode(LAT);
//                Expr_gen(0);
                tocode(SLICE);
            }
                break;
                
            case TCall1:
            {
                int i, n = tree[++tc];
                tc++;
                tocode(CALL1);
                for (i=0; i < n; i++)
                    Expr_gen(0);
            }
                break;
                
            case TCall2:
            {
                tc++;
                tocode(CALL2);
                tocode(identab[-tree[tc++]+3]);
            }
                break;
        }
        
        while ((c = tree[tc]) > 0)
        {
            tc++;
            if (c != NOP)
            {
                tocode(c);

                if ((c >= ASS && c <= DIVASS) || (c >= ASSV && c <= DIVASSV) ||
                    (c >= PLUSASSR && c <= DIVASSR) || (c >= PLUSASSRV && c <= DIVASSRV) ||
                    (c >= POSTINC && c <= DEC) || (c >= POSTINCV && c <= DECV) ||
                    (c >= POSTINCR && c <= DECR) || (c >= POSTINCRV && c <= DECRV))
                {
                    tocode(identab[- tree[tc++] + 3]);
                }
 
            }
        }
        
        if (tree[tc] == TCondexpr)
        {
            int adelse, ad;
            int thenref = tree[++tc], elseref = tree[++tc];
            tc++;
            tocode(BE0);
            adelse = pc++;
            Expr_gen(0);              // then
            tocode(B);
            ad = pc;
            mem[pc++] = adfi;
            mem[adelse] = pc;
            Expr_gen(pc-1);           // else или cond
            if (tree[tc] != TCondexpr)
                while (ad)
                {
                    int r = mem[ad];
                    mem[ad] = pc;
                    ad = r;
                }
            if (adfi)
                return;
        }
            while ((c = tree[tc]) > 0)
            {
                tc++;
                if (c != NOP)
                {
                    tocode(c);
                    if ((c >= ASS && c <= DIVASS) || (c >= ASSV && c <= DIVASSV) ||
                        (c >= PLUSASSR && c <= DIVASSR) || (c >= PLUSASSRV && c <= DIVASSRV) ||
                        (c >= POSTINC && c <= DEC) || (c >= POSTINCV && c <= DECV) ||
                        (c >= POSTINCR && c <= DECR) || (c >= POSTINCRV && c <= DECRV))
                    {
                        tocode(identab[- tree[tc++] + 3]);
                    }
                }
            }
        
        if (tree[tc] == TExprend)
        {
             tc++;
             flagprim = 0;
        }
    }
}

void compstmt_gen();

void Stmt_gen()
{
    switch (tree[tc++])
    {
        case TBegin:
        {
            compstmt_gen();
        }
            break;
            
        case TIf:
        {
            int thenref = tree[tc++], elseref = tree[tc++], ad;
            Expr_gen(0);
            tocode(BE0);
            ad = pc++;
            Stmt_gen();
            if (elseref)
            {
                mem[ad] = pc + 2;
                tocode(B);
                ad = pc++;
                Stmt_gen();
            }
            mem[ad] = pc;
        }
            break;
            
        case TWhile:
        {
            int doref = tree[tc++];
            int oldbreak = adbreak, oldcont = adcont, ad = pc;
            adcont = 0;
            Expr_gen(0);
            tocode(BE0);
            mem[pc] = 0;
            adbreak = pc++;
            Stmt_gen();
            adcontend();
            tocode(B);
            tocode(ad);
            adbreakend();
            adbreak = oldbreak;
            adcont = oldcont;
        }
            break;

        case TDo:
        {
            int condref = tree[tc++];
            int oldbreak = adbreak, oldcont = adcont, ad = pc;
            adbreak = 0;
            adcont = 0;
            Stmt_gen();
            adcontend();
            Expr_gen(0);
            tocode(BNE0);
            tocode(ad);
            adbreakend();
            adbreak = oldbreak;
            adcont = oldcont;
        }
            break;

        case TFor:
        {
            int fromref = tree[tc++], condref = tree[tc++], incrref = tree[tc++], stmtref = tree[tc++];
            int oldbreak = adbreak, oldcont = adcont, ad = pc, incrtc, endtc;
            adcont = 0;
            if (fromref)
            {
                Expr_gen(0);         // init
            }
            ad = pc;
            if (condref)
            {
                Expr_gen(0);         // cond
                tocode(BE0);
                mem[pc] = 0;
                adbreak = pc++;
            }
            incrtc = tc;
            tc = stmtref;
            Stmt_gen();             //  ???? был 0
            adcontend();
            if (incrref)
            {
                endtc = tc;
                tc = incrtc;
                Expr_gen(0);         // incr
                tc = endtc;
            }
            tocode(B);
            tocode(ad);
            adbreakend();
            adbreak = oldbreak;
            adcont = oldcont;
        }
            break;
            
        case TGoto:
        {
            int id1 = tree[tc++], a;
            int id = id1 > 0 ? id1 : -id1;
            tocode(B);
            if ( (a = identab[id+3]) > 0)           // метка уже описана
                tocode(a);
             else                                   // метка еще не описана
             {
                identab[id+3] = -pc;
                tocode(id1 < 0 ? 0 : a);            // первый раз встретился переход на еще не описанную метку или нет
             }
        }
            break;
    
        case TLabel:
        {
            int id = tree[tc++], a;
            if ((a = identab[id+3]) < 0)            // были переходы на метку
                while (a)                           // проставить ссылку на метку во всех ранних переходах
                {
                    int r = mem[-a];
                    mem[-a] = pc;
                    a = r;
                }
            identab[id+3] = pc;
        }
            break;
            
        case TSwitch:
        {
            int oldbreak = adbreak, oldcase = adcase;
            adbreak = 0;
            adcase = 0;
            Expr_gen(0);
            Stmt_gen();
            if (adcase > 0)
                mem[adcase] = pc;
            adcase = oldcase;
            adbreakend();
            adbreak = oldbreak;
        }
            break;

        case TCase:
        {
            if (adcase)
                mem[adcase] = pc;
            tocode(DOUBLE);
            Expr_gen(0);
            tocode(EQEQ);
            tocode(BE0);
            adcase = pc++;
            Stmt_gen();
        }
            break;

        case TDefault:
        {
            if (adcase)
                mem[adcase] = pc;
            Stmt_gen();
        }
            break;

        case TBreak:
        {
            tocode(B);
            mem[pc] = adbreak;
            adbreak = pc++;
        }
            break;
            
        case TContinue:
        {
            tocode(B);
            mem[pc] = adcont;
            adcont = pc++;
        }
            break;

        case TReturn:
        {
            tocode(RETURNV);
        }
            break;

        case TReturnval:
        {
            Expr_gen(0);
            tocode(_RETURN);
        }
            break;
    
        case TPrint:
        {
            tocode(PRINT);
            tocode(tree[tc++]);  // type
        }
            break;
            
        case TPrintid:
        {
            tocode(PRINTID);
            tocode(tree[tc++]);  // ссылка в identtab
        }
            break;
            
        case TGetid:
        {
            tocode(GETID);
            tocode(tree[tc++]);  // ссылка в identtab
        }
            break;
            
        default:
        {
            tc--;
            Expr_gen(0);
        }
            break;
    }
}

void Declid_gen()
{
    int identref = tree[tc++], initref = tree[tc++], N = tree[tc++];
    int olddispl = identab[identref+3], i;
    if (N == 0)
    {
        if (initref)
        {
            Expr_gen(0);
            tocode(ASSV);
            tocode(olddispl);
        }
    }
    else if (N == 1)
    {
        Expr_gen(0);
        tocode(DEFARR);
        tocode(olddispl);
        if (initref)
        {
            tc++;               // INIT
            int L = tree[tc++];
            for (i=0; i<L; i++)
                Expr_gen(0);
            tocode(ASSARR);
            tocode(olddispl);
            tocode(L);
        }
    }
    else               // N==2
    {
        Expr_gen(0);
        Expr_gen(0);
        tocode(DEFARR2);
        tocode(olddispl);
        if (initref)
        {
            tc++;               // INIT
            int L = tree[tc++];
            for (i=0; i<L; i++)
                Expr_gen(0);
            tocode(ASSARR2);
            tocode(olddispl);
            tocode(L);
        }
    }
    
}

void compstmt_gen()
{
    while (tree[tc] != TEnd)
    {
        switch (tree[tc])
        {
            case TDeclid:
                tc++;
                Declid_gen();
                break;
                
            default:
                Stmt_gen();
        }
    }
    tc++;
}
void codegen()
{
    int oldtc = tc;
    tc = 0;
    while (tc < oldtc)
        switch (tree[tc++])
    {
        case TFuncdef:
        {
            int identref = tree[tc++], maxdispl = tree[tc++];
            int fn = identab[identref+3], pred;
            functions[fn]= pc;
            tocode(FUNCBEG);
            tocode(maxdispl+1);
            pred = pc++;
            tc++;             // TBegin
            compstmt_gen();
            mem[pred] = pc;
        }
            break;
            
        case TDeclid:
            Declid_gen();
            
            break;
            
        default:
        {
            printf("что-то не то\n");
            printf("tc=%i tree[tc-2]=%i tree[tc-1]=%i\n", tc, tree[tc-2], tree[tc-1]);
        }
    }
    
    if (wasmain == 0)
        error(no_main_in_program);
    tocode(CALL1);
    tocode(CALL2);
    tocode(identab[wasmain+3]);
    tocode(STOP);

}
