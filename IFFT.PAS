PROGRAM IFFT;
{
****************************************************************************
 Vers„o em XView do programa IFFT
 Por Ant“nio Carlos Moreir„o de Queiroz
 Versao 0 de 02/02/92 - Calculo da ordem
 Versao 1.0 de 16/04/92 - Tudo e mantido normalizado, mesmo valores salvos
 Versao 1.0a de 31/05/92 - Corrigida inicializacao da jedit, fz correto
 Versao 1.0b de 04/06/92 - Calculo de raizes separado do dos polinomios
 Versao 1.0c de 11/06/92 - Calculo de raizes por Birge-Vieta incluido
 Versao 1.0d de 26/06/92 - Calculo de raizes direto pelo menu
 Versao 1.0e de 11/07/92 - Messages em preto e funcao Saida
 Versao 1.0f de 17/07/92 - Corrigida posicao do girador na arvore normal
 Versao 1.0g de 01/08/92 - Janela de diretorio
 Versao 1.0h de 27/09/92 - Abre janela de diretorio no inicio (XView 1.4c)
 Versao 1.1  de 19/10/92 - Analise Nodal Modificada normalizada; Fonte Z
 Versao 1.1a de 01/11/92 - Erro maluco no 80387 detectado em Ex. Graufft ok
 Versao 1.1b de 19/05/93 - Erro fatal por grau excessivo
 Versao 1.1c de 28/06/93 - Renomeado IFFT
 Versao 1.2  de 25/08/93 - Varredura e rearrumacao
 Versao 1.2a de 18/01/94 - Zoom out na resp. freq. e aviso de singularidade
 Versao 1.2b de 22/08/95 - Melhorada geracao da arvore normal
 Versao 1.3  de 26/08/95 - Analise de Monte Carlo. Salva referencias.
 Versao 1.3a de 08/11/95 - Corrigida posicao de Gds no transistor MOS.
 Versao 1.3b de 17/10/96 - Corrigido no de terra do amplificador.
 Versao 1.4  de 07/03/01 - Transformador com k.
 Versao 1.5  de 09/10/08 - VCCS com ganho de modo comum.
 Versao 1.5a de 05/11/08 - AmpOp com 4 terminais e comentarios aceitos.
 Versao 1.5b de 13/11/08 - Amplificador com 4 terminais. Aceita o antigo.
 Versao 1.6  de 22/06/11 - Transformador com letra K.

 A implementar:
   Calculo da amostra significativa para Monte Carlo.
   Salvar polos e zeros desnormalizados?
   Matrizes em pointers
   Analise nodal modificada compacta?
   Capacitancias nos transistores?
   Estrutura do netlist interno mais simples?
   Melhores cursores, que nao marquem as bordas
   Imprimir graficos?
****************************************************************************
}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Dos,Graph,Crt,Saida_e,Mickey,XView;

{$IFNDEF DOUBLE}
TYPE
  DOUBLE=REAL;
{$ENDIF}

CONST
  versao='1.6 - 22/06/2011';
  fl=^M^J;
  tamnome=5;
  MaxEl=170;
  wmin0:REAL=0.2;
  wmax0:REAL=5;
  gmin0:REAL=-80;
  gmax0:REAL=10;
  MaxNos={$IFDEF EXTENDED} 40 {$ELSE} 45 {$ENDIF};
  MaxNos1=MaxNos+1;
  MaxNosAntes=50;
  Grmax=31;
  Gmax2=2*Grmax;
  MeioGm=(Grmax+1) div 2;
  maxref={$IFDEF EXTENDED} 250 {$ELSE} 400 {$ENDIF};
  xxmax=199;
  nref:INTEGER=0;
  netlist_lido:BOOLEAN=FALSE;
  analise_feita:BOOLEAN=FALSE;
  resposta_plotada:BOOLEAN=FALSE;
  raizes_plotadas:BOOLEAN=FALSE;

TYPE
  componente=(FonteV,VCVS,CCVS,CCCS,Capacitor,Resistor,FonteF,Amplificador,MOS,BJT,Girador,
              Indutor,Transformador,VCCS,FonteI,AmpOp);
  elemento=RECORD
    tipo:componente;
    nome:STRING[tamnome];
    no:ARRAY[1..6] of BYTE;
    val:ARRAY[1..4] of REAL
  END;
  polinomio=Array[0..Grmax] of REAL;
  raizes=Array[1..Grmax] of DOUBLE;
  curva=ARRAY[0..xxmax] OF DOUBLE;
  fdet=
    RECORD
      nome:STRING;
      ngrau,dgrau:INTEGER;
      Num,Den:polinomio;
      cted,cten:REAL;
      fator:REAL; {fator de normalizacao em frequencia}
      ga,fa,ta:INTEGER;
      Gan,Fas,Tg:curva;
      numerador_valido,denominador_valido:BOOLEAN;
      zeros_validos,polos_validos:BOOLEAN;
      RePolos,ImPolos,ReZeros,ImZeros:raizes;
    END;
  ListaNet=ARRAY[1..MaxEl] of elemento;
  cores=ARRAY[-1..maxref] OF BYTE;

CONST
  biblioteca:ARRAY[componente] of RECORD
    letra:CHAR;
    nnos:BYTE;
    nmno:ARRAY[1..4] of STRING[2];
    nval:BYTE;
    nmval:ARRAY[1..4] of STRING[3];
  END
  =(
    (letra:'V'; nnos:2; nmno:('V+','V-','',''); nval:1; nmval:('V','','','')),
    (letra:'E'; nnos:4; nmno:('V+','V-','v+','v-'); nval:1; nmval:('Av','','','')),
    (letra:'H'; nnos:4; nmno:('V+','V-','i+','i-'); nval:1; nmval:('Rm','','','')),
    (letra:'F'; nnos:4; nmno:('I+','I-','i+','i-'); nval:1; nmval:('Ai','','','')),
    (letra:'C'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('C','','','')),
    (letra:'R'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('R','','','')),
    (letra:'Z'; nnos:2; nmno:('V-','V+','',''); nval:2; nmval:('Rs','Vs','','')),
    (letra:'A'; nnos:4; nmno:('o+','o-','i-','i+'); nval:2; nmval:('GB','Ro','','')),
    (letra:'M'; nnos:3; nmno:('d','g','s',''); nval:2; nmval:('Gm','Gds','','')),
    (letra:'Q'; nnos:3; nmno:('c','b','e',''); nval:4; nmval:('hfe','hie','hre','hoe')),
    (letra:'Y'; nnos:4; nmno:('11','12','21','22'); nval:1; nmval:('Rg','','','')),
    (letra:'L'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('L','','','')),
    (letra:'K'; nnos:4; nmno:('11','12','21','22'); nval:3; nmval:('L11','L22','k12','')),
    (letra:'G'; nnos:4; nmno:('I+','I-','V+','V-'); nval:2; nmval:('Gm','Gc','','')),
    (letra:'I'; nnos:2; nmno:('I+','I-','',''); nval:1; nmval:('Is','','','')),
    (letra:'O'; nnos:4; nmno:('o+','o-','i','i'); nval:0; nmval:('','','',''))
   );
  primeiro_tipo=FonteV;
  ultimo_tipo=AmpOp;
VAR
  cor:cores;
  netlist:ListaNet;
  C,L:ARRAY[0..MaxNosAntes] of INTEGER;
  Yr,Yi:ARRAY[0..MaxNos,0..MaxNos1] of REAL;
  Nr,Ni:ARRAY[1..MaxNos,0..MeioGm] of REAL;
  Dr,Di:ARRAY[0..MeioGm] of REAL;
  Frq:ARRAY[0..xxmax] OF DOUBLE;
  AA,BB:polinomio;
  menu1,menu2,menu3:Xv_opaque;
  botao,bmais:Xv_opaque;
  jfrequencia,cresposta:Xv_opaque;
  jparametros,tdispden,tdispnum,tfatorw,tfatorz,tngrau,tdgrau,tsaida,sforcar,sraizes:Xv_opaque;
  jextra,ttol,ttolm,treal,timag,tminimo,smetodo:Xv_opaque;
  jterminal,ttymsg:Xv_opaque;
  jpfrequencia,twmin,twmax,tgmin,tgmax,tfmin,tfmax,tamin,tamax,slog,srads,splotar,snorm,tsegmentos:Xv_opaque;
  jedit,tenome:Xv_opaque;
  tvalor:ARRAY[1..4] of Xv_opaque;
  jraizes,craizes:Xv_opaque;
  jreferencia,ttitulo,tnsaida,tnumerador,tdenominador,tpolos,tzeros:Xv_opaque;
  jdiretorio,cdiretorio,tmask,tnetlist:Xv_opaque;
  jsweep,tswval,tswel,ssweep,tswmin,tswmax,tswn,sescala:Xv_opaque;
  jmontecarlo,tmonten,tmontetr,tmontetlcm,sdistribuicao:Xv_opaque;
  placa,modo,iii:INTEGER;
  nos,nosantes,nosmesmo,numero,ind,graufft,ordem,eedit:INTEGER;
  Imag,fatorz,fatord,ang,sr,si,vr,vi,mden,fwd,fzd:REAL;
  arquivo:TEXT;
  ok,numerador:BOOLEAN;
  rede,txt:STRING;
  funcao:ARRAY[0..maxref] OF ^fdet;
  r:CHAR;
  DoisPi,LnDb,RadGraus:REAL;
  i:INTEGER;

VAR
  ah,bh,ag,bg,af,bf,at,bt,aw,bw,dx,w,a1,a2,b1,b2,da1,da2,db1,db2,f:REAL;
  t1,t2,t:REAL;
  xa,xq,yq,atual,ultpt,ix,csr,xmin,xmax,ymin,ymax,xpmax,ypmax:INTEGER;
  {polos e zeros}
  immin,remin,delta,ay,by,ax,bx:REAL;
  basex,basey:INTEGER;
  polos:BOOLEAN;

CONST
  unid:ARRAY[BOOLEAN] OF STRING[5]=('Hz','rad/s');
  cor_fraca=-1;
  modo1:BOOLEAN=TRUE;

{$I setas.p}

{$F+}
PROCEDURE InvalidarAnalise(obj:Xv_opaque);FORWARD;
{$F-}

{Distribuicao Gaussiana com variancia unitaria (Numerical Recipes)}
CONST
  iset:INTEGER=0;
VAR
  gset:REAL;

FUNCTION RandGauss:REAL;
VAR
  fac,r,v1,v2:REAL;
BEGIN
  IF iset=0 THEN BEGIN
    REPEAT
      v1:=2*Random-1;
      v2:=2*Random-1;
      r:=Sqr(v1)+Sqr(v2)
    UNTIL (r<1) and (r<>0);
    fac:=Sqrt(-2*Ln(r)/r);
    gset:=v1*fac;
    iset:=1;
    RandGauss:=v2*fac
  END
  ELSE BEGIN
    iset:=0;
    RandGauss:=gset
  END;
END;

PROCEDURE Saida(txt:STRING);
BEGIN
  ttysw_output(ttymsg,txt+fl);
END;

PROCEDURE ErroFatal(texto:STRING);
BEGIN
  Saida(#13#10+'* Error: '+texto);
  Saida('Touch a key to quit...');
  REPEAT UNTIL KeyPressed;
  TextMode(80);
  Halt
END;

PROCEDURE ApagarTela;
BEGIN
  WITH ttymsg^ DO yc:=dy;
  ttysw_output(ttymsg,'');
END;

PROCEDURE Inverter(obj:Xv_opaque; b:INTEGER);
BEGIN
  WITH obj^ DO sel_setting:=sel_setting xor b;
END;

FUNCTION Teste(obj:Xv_opaque; b:INTEGER):BOOLEAN;
BEGIN
  WITH obj^ DO Teste:=sel_setting and b=b
END;

FUNCTION Log:BOOLEAN;
BEGIN
  Log:=slog^.sel_setting=1
END;

FUNCTION Rads:BOOLEAN;
BEGIN
  Rads:=srads^.sel_setting=1
END;

FUNCTION Normalizar:BOOLEAN;
BEGIN
  Normalizar:=snorm^.sel_setting=1
END;

FUNCTION Sri(x:LONGINT):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x,tmp);
  Sri:=tmp
END;

FUNCTION Sre(x:REAL; cm,dc:SHORTINT):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x:cm:dc,tmp);
  Sre:=tmp
END;

FUNCTION NomeAtual(atual:INTEGER):STRING;
VAR
  i:INTEGER;
BEGIN
  WITH Funcao[atual]^ DO BEGIN
    i:=Length(nome);
    WHILE (i>0) and (nome[i]<>'\') DO Dec(i);
    txt:=Copy(nome,i+1,255);
    IF atual>0 THEN txt:=txt+' (#'+Sri(atual)+')';
    NomeAtual:=txt
  END
END;

FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;  {Multiplicacao complexa}
BEGIN
  Cmult:=x1*y1-x2*y2;
  Imag:=x1*y2+x2*y1
END; {Cmult}

FUNCTION Ex(x:REAL;t:REAL):REAL;
BEGIN
 {O 80387 da um erro maluco na representacao de 4-2e-19}
 Ex:=Exp(t*Ln(x+2e-19))
END;

PROCEDURE AcharOrdem;
CONST
  maxteste=19;
  prioridade:ARRAY[1..maxteste] OF RECORD cmp:componente; tr1,tr2,lado:BYTE END
  =(
  (cmp:FonteV;tr1:1;tr2:2;lado:1),
  (cmp:CCVS;tr1:3;tr2:4;lado:1),
  (cmp:CCCS;tr1:3;tr2:4;lado:1),
  (cmp:VCVS;tr1:1;tr2:2;lado:1),
  (cmp:CCVS;tr1:1;tr2:2;lado:2),
  (cmp:Capacitor;tr1:1;tr2:2;lado:1),
  (cmp:FonteF;tr1:1;tr2:2;lado:1),
  (cmp:Amplificador;tr1:1;tr2:2;lado:1),
  (cmp:BJT;tr1:2;tr2:3;lado:1),
  (cmp:Resistor;tr1:1;tr2:2;lado:1),
  (cmp:BJT;tr1:1;tr2:3;lado:2),
  (cmp:MOS;tr1:1;tr2:3;lado:1),
  (cmp:Girador;tr1:1;tr2:2;lado:1), {fontes de corrente antes de L prevendo giradores}
  (cmp:Girador;tr1:3;tr2:4;lado:2),
  (cmp:VCCS;tr1:1;tr2:2;lado:1),
  (cmp:CCCS;tr1:1;tr2:2;lado:2),
  (cmp:Indutor;tr1:1;tr2:2;lado:1),
  (cmp:Transformador;tr1:1;tr2:2;lado:1),
  (cmp:Transformador;tr1:3;tr2:4;lado:2)
  );

VAR
  ok:BOOLEAN;
  temp:elemento;
  arvore:ARRAY[0..MaxNosAntes] OF INTEGER;
  marcado:ARRAY[1..MaxEl] OF WORD;
  nosarvore,e,nosreais:INTEGER;
  tipo_em_teste:INTEGER;
  graudefault:INTEGER;

  PROCEDURE TentarIncluir(no1,no2,ramo:INTEGER);
  VAR
    i:INTEGER;
    um,dois:BOOLEAN;
  BEGIN
    IF (marcado[e] and ramo)=ramo THEN Exit;
    um:=FALSE; dois:=FALSE;
    FOR i:=0 TO nosarvore DO BEGIN
      IF arvore[i]=L[no1] THEN um:=TRUE;
      IF arvore[i]=L[no2] THEN dois:=TRUE
    END;
    IF um xor dois THEN BEGIN
      Inc(nosarvore);
      ok:=TRUE;
      IF um THEN arvore[nosarvore]:=L[no2]
      ELSE arvore[nosarvore]:=L[no1];
      Inc(marcado[e],ramo);
      WITH netlist[e] DO
      Saida(nome+', nodes '+Sri(no1)+' and '+Sri(no2));
    END
  END;

BEGIN
  nosarvore:=0;
  arvore[0]:=0;
  nosreais:=nos-(nosantes-nosmesmo);
  FOR e:=1 TO numero DO marcado[e]:=0;
  Saida('Normal tree branches:');
  REPEAT
    tipo_em_teste:=1;
    REPEAT
      e:=1; ok:=FALSE;
      WITH prioridade[tipo_em_teste] DO
        REPEAT
          WITH netlist[e] DO
            IF tipo=cmp THEN
               TentarIncluir(no[tr1],no[tr2],lado);
          Inc(e)
        UNTIL (e>numero) or ok;
      Inc(tipo_em_teste);
    UNTIL ok or (tipo_em_teste>maxteste);
    IF not ok and (tipo_em_teste>maxteste) THEN Saida('* Part of the network is floating');
  UNTIL (nosarvore=nosreais) or (tipo_em_teste>maxteste);
  graudefault:=0; ind:=0;
  FOR e:=1 TO numero DO WITH NetList[e] DO CASE tipo OF
    Capacitor:IF marcado[e]=1 THEN BEGIN
      Inc(graudefault)
    END;
    Indutor:BEGIN
      Inc(ind);
        IF marcado[e]=0 THEN BEGIN
          Inc(graudefault)
        END
      END;
    Amplificador:BEGIN
      Inc(graudefault); Inc(ind)
    END;
    Transformador:BEGIN
      IF marcado[e]=0 THEN Inc(graudefault,2)
      ELSE IF marcado[e]<3 THEN Inc(graudefault);
      Inc(ind,2)
    END;
  END;
  Saida('Maximum complexity order: '+Sri(graudefault));
  Saida('Number of elements in 1/s: '+Sri(ind));
  tdgrau^.panel_int:=graudefault;
  tngrau^.panel_int:=graudefault;
END;

PROCEDURE LerNetList;
VAR
  leutudo:BOOLEAN;
  r:CHAR;
  cp:componente;
  i,p,a1,b1,c1,d1:INTEGER;
  buf:ARRAY[1..8] OF REAL;

LABEL Achou,Fim,Continuar;

PROCEDURE TestarNos;
  BEGIN
    IF nosantes>MaxNosAntes THEN ErroFatal('The maximum number of nodes is '+Sri(MaxNosAntes));
  END;

BEGIN
  netlist_lido:=FALSE;
  ReadLn(arquivo,nosantes); nos:=nosantes; nosmesmo:=nos;
  ApagarTela;
  Saida('Circuit: '+rede);
  Saida('Number of nodes: '+Sri(nosmesmo));
  TestarNos;
  FOR i:=0 TO MaxNosAntes DO BEGIN C[i]:=i; L[i]:=i END;
  Saida('Circuit description:');
  numero:=1; ind:=0;
  REPEAT
    IF numero>MaxEl THEN ErroFatal('The maximum number of effective elements is '+Sri(MaxEl));
    WITH netlist[numero] DO BEGIN
      Read(arquivo,r);
      IF r='*' THEN BEGIN
        ReadLn(arquivo,txt);
        Saida(r+txt);
        GoTo Continuar
      END;
      nome:=Upcase(r);
      REPEAT
        Read(arquivo,r);
        IF r<>' ' THEN nome:=nome+UpCase(r)
      UNTIL (r=' ') or (Length(nome)=tamnome);
      FOR cp:=primeiro_tipo TO ultimo_tipo DO
        WITH biblioteca[cp] DO
          IF nome[1]=letra THEN BEGIN
            leutudo:=TRUE;
            tipo:=cp;
            FOR i:=1 TO nnos+nval DO
              IF not SeekEoln(arquivo) THEN Read(arquivo,buf[i])
              ELSE BEGIN
                leutudo:=FALSE;
                buf[i]:=0;
              END;
            FOR i:=1 TO nnos DO
              IF Abs(buf[i])<=MaxNos THEN no[i]:=Round(buf[i])
              ELSE no[i]:=0;
            FOR i:=1 to nval DO val[i]:=buf[nnos+i];
            ReadLn(arquivo);
            txt:=nome+': ';
            { Casos especiais }
            CASE tipo OF
              {VCCS:IF not leutudo THEN val[2]:=0;}
              FonteF:IF not leutudo THEN val[2]:=1;
              FonteV,VCVS,CCCS:BEGIN
                Inc(nosantes); Inc(nos);
                TestarNos;
                no[5]:=nosantes;
                txt:=txt+Sri(nosantes)+'(j) ';
              END;
              CCVS:BEGIN
                Inc(nosantes,2); Inc(nos,2);
                TestarNos;
                no[5]:=nosantes-1;
                no[6]:=nosantes;
                txt:=txt+Sri(no[5])+'(j1) '+Sri(no[6])+'(j2) '
              END;
              Amplificador: IF not leutudo THEN BEGIN
                c1:=no[2]; d1:=no[1]; a1:=no[3];
                no[1]:=a1; no[2]:=0; no[3]:=d1; no[4]:=c1;
                val[1]:=buf[4]; val[2]:=buf[5];
              END;
              AmpOp: IF not leutudo THEN BEGIN
                c1:=no[2]; d1:=no[1]; a1:=no[3];
                no[1]:=a1; no[2]:=0; no[3]:=d1; no[4]:=c1; {1.5a}
              END;
            END;
            FOR i:=1 TO nnos DO txt:=txt+Sri(no[i])+'('+nmno[i]+') ';
            FOR i:=1 TO nval DO txt:=txt+nmval[i]+':'+Cpct(val[i])+' ';
            Saida(txt);
            GoTo Achou
          END;
      Saida('* Unknown element: '+nome);
      GoTo Fim;
     Achou:
      IF tipo<>AmpOp THEN Inc(numero)
      ELSE BEGIN
        IF (C[no[3]]>C[no[4]]) THEN BEGIN c1:=C[no[4]]; d1:=C[no[3]] END
        ELSE BEGIN c1:=C[no[3]]; d1:=C[no[4]] END;
        IF (L[no[1]]>L[no[2]]) THEN BEGIN a1:=L[no[2]]; b1:=L[no[1]] END
        ELSE BEGIN a1:=L[no[1]]; b1:=L[no[2]] END;
        IF (a1=b1) OR (c1=d1) THEN ErroFatal('Invalid circuit');
        FOR i:=1 TO MaxNosAntes DO BEGIN
          IF C[i]=d1 THEN C[i]:=c1;
          IF C[i]>d1 THEN Dec(C[i]);
          IF L[i]=b1 THEN L[i]:=a1;
          IF L[i]>b1 THEN Dec(L[i])
        END;
        Dec(nos)
      END
    END;
    Continuar:
  UNTIL SeekEof(arquivo);
  Dec(numero);
  Saida('Number of effective elements: '+Sri(numero));
  Saida('Number of independent variables: '+Sri(nos));
  IF nos>MaxNos THEN ErroFatal('The maximum number of independent variables is '+Sri(MaxNos));
  AcharOrdem;
  netlist_lido:=TRUE;
  tsaida^.max_value:=nosantes;
  eedit:=1;
  close_window(jedit);
  close_window(jsweep);
  WITH netlist[eedit] DO WITH biblioteca[tipo] DO BEGIN
     tenome^.xv_label:=nome;
     FOR i:=1 TO 4 DO WITH tvalor[i]^ DO
       IF i<=nval THEN BEGIN
         panel_real:=val[i];
         xv_label:=nmval[i]
       END
       ELSE BEGIN
         panel_real:=0;
         xv_label:='-';
       END
  END;
  InvalidarAnalise(nil);
 Fim:
  Close(arquivo)
END; {LerNetList}

PROCEDURE TransAdmitancia(a,b:REAL; n1,n2,n3,n4:INTEGER; norm:BOOLEAN);
BEGIN
  IF norm THEN BEGIN a:=a*fatorz; b:=b*fatorz END;
  Yr[L[n1],C[n3]]:=Yr[L[n1],C[n3]]+a;
  Yr[L[n2],C[n4]]:=Yr[L[n2],C[n4]]+a;
  Yr[L[n1],C[n4]]:=Yr[L[n1],C[n4]]-a;
  Yr[L[n2],C[n3]]:=Yr[L[n2],C[n3]]-a;
  Yi[L[n1],C[n3]]:=Yi[L[n1],C[n3]]+b;
  Yi[L[n2],C[n4]]:=Yi[L[n2],C[n4]]+b;
  Yi[L[n1],C[n4]]:=Yi[L[n1],C[n4]]-b;
  Yi[L[n2],C[n3]]:=Yi[L[n2],C[n3]]-b
END; {TransAdmitancia}

PROCEDURE Admitancia(a,b:REAL; n1,n2:INTEGER);
BEGIN
  TransAdmitancia(a,b,n1,n2,n1,n2,TRUE)
END; {Admitancia}

PROCEDURE Corrente(I:REAL; a,b:INTEGER);
BEGIN
  Yr[L[a],nos+1]:=Yr[L[a],nos+1]-I;
  Yr[L[b],nos+1]:=Yr[L[b],nos+1]+I;
END;

PROCEDURE Gyrator(a,b,c:INTEGER);
BEGIN
  TransAdmitancia(1,0,a,b,c,0,FALSE);
  TransAdmitancia(1,0,0,c,a,b,FALSE)
END;

PROCEDURE MontarSistema;
VAR
  i,j:INTEGER;
  t,t1:REAL;
BEGIN
  FOR i:=0 TO nos DO
    FOR j:=0 TO nos+1 DO BEGIN Yr[i,j]:=0; Yi[i,j]:=0 END;
  FOR i:=1 to numero DO
  WITH NetList[i] DO BEGIN
    CASE tipo OF
      Resistor:Admitancia(1/val[1],0,no[1],no[2]);
      Indutor:BEGIN
          t:=val[1]*(Sqr(sr)+Sqr(si));
          Admitancia(sr/t,-si/t,no[1],no[2])
        END;
      Capacitor:Admitancia(sr*val[1],si*val[1],no[1],no[2]);
      Amplificador:BEGIN
          { Y12=-GB/sRo; Y22=1/Ro }
          Admitancia(1/val[2],0,no[1],no[2]);
          t:=val[1]/val[2]/(Sqr(sr)+Sqr(si));
          TransAdmitancia(t*sr,-t*si,no[1],no[2],no[3],no[4],TRUE);
        END;
      VCCS:BEGIN {Transcondutor, possivelmente com ganho de modo comum}
        TransAdmitancia(val[1],0,no[1],no[2],no[3],no[4],TRUE);
        TransAdmitancia(-val[2]/2,0,no[1],0,no[3],0,TRUE);
        TransAdmitancia(-val[2]/2,0,no[2],0,no[3],0,TRUE);
        TransAdmitancia(-val[2]/2,0,no[1],0,no[4],0,TRUE);
        TransAdmitancia(-val[2]/2,0,no[2],0,no[4],0,TRUE);
      END;
      FonteF:BEGIN {Fonte com resistor s‚rie}
        Corrente(fatorz*val[2]/val[1],no[1],no[2]);
        Admitancia(1/val[1],0,no[1],no[2])
      END;
      FonteI:Corrente(fatorz*val[1],no[1],no[2]); {Fonte de corrente}
      Girador:BEGIN
          { Y12=1/R Y21=-1/R }
          TransAdmitancia(1/val[1],0,no[1],no[2],no[3],no[4],TRUE);
          TransAdmitancia(1/val[1],0,no[4],no[3],no[1],no[2],TRUE)
        END;
      Transformador:BEGIN
          { Det(L)=L1L2(1-k^2) }
          { Y11=L2/sDet(L) }
          { Y22=L1/sDet(L) }
          { Y12=-M12/sDet(L) }
          { Y21=-M21/sDet(L) }
          t:=val[1]*val[2]*(1-sqr(val[3]))*(Sqr(sr)+Sqr(si));
          t1:=val[2]/t;  {Y11}
          Admitancia(t1*sr,-t1*si,no[1],no[2]);
          t1:=val[1]/t;  {Y22}
          Admitancia(t1*sr,-t1*si,no[3],no[4]);
          t1:=-val[3]*sqrt(val[1]*val[2])/t; {Y12=Y21}
          TransAdmitancia(t1*sr,-t1*si,no[1],no[2],no[3],no[4],TRUE);
          TransAdmitancia(t1*sr,-t1*si,no[3],no[4],no[1],no[2],TRUE);
        END;
      MOS:BEGIN
            Transadmitancia(val[1],0,no[1],no[3],no[2],no[3],TRUE); {Gm}
            Admitancia(val[2],0,no[1],no[3]) {Gds}
          END;
      BJT:BEGIN
          Admitancia(1/val[2],0,no[2],no[3]); {hie}
          Admitancia(val[4],0,no[1],no[3]);   {hoe}
          TransAdmitancia(val[1]/val[2],0,no[1],no[3],no[2],no[3],TRUE);  {hfe/hie}
          TransAdmitancia(val[3]/val[2],0,no[3],no[2],no[1],no[3],TRUE);  {hre/hie}
          TransAdmitancia(val[3]*val[1]/val[2],0,no[1],no[3],no[3],no[1],TRUE); {hre*hfe/hie}
        END;
      FonteV:BEGIN
          Gyrator(no[1],no[2],no[5]);
          Corrente(val[1],no[5],0)
        END;
      VCVS:BEGIN
          Gyrator(no[1],no[2],no[5]);
          TransAdmitancia(val[1],0,no[5],0,no[3],no[4],FALSE)
        END;
      CCCS:BEGIN
          TransAdmitancia(val[1],0,no[1],no[2],no[5],0,FALSE);
          Gyrator(no[3],no[4],no[5])
        END;
      CCVS:BEGIN
          TransAdmitancia(val[1]/fatorz,0,no[6],0,no[5],0,FALSE);
          Gyrator(no[1],no[2],no[6]);
          Gyrator(no[3],no[4],no[5])
        END
    END
  END
END; {MontarSistema}

PROCEDURE ResolverSistema;
VAR
  qr,qi,tr,ti,t:REAL;
  i,j,k,m:INTEGER;
BEGIN
  vr:=Cos(ind*ang); vi:=Sin(ind*ang);
  FOR i:=1 TO nos DO BEGIN
    tr:=0; ti:=0; m:=i;
    FOR k:=i TO nos DO
      IF Abs(Yr[k,i])+Abs(Yi[k,i])>Abs(tr)+Abs(ti) THEN BEGIN
        m:=k;
        tr:=Yr[k,i];
        ti:=Yi[k,i]
      END;
    IF i<>m THEN BEGIN
      vi:=-vi; vr:=-vr;
      FOR k:=i TO nos+1 DO BEGIN
        t:=Yr[i,k];
        Yr[i,k]:=Yr[m,k];
        Yr[m,k]:=t;
        t:=Yi[i,k];
        Yi[i,k]:=Yi[m,k];
        Yi[m,k]:=t
      END
    END;
    vr:=Cmult(vr,vi,tr,ti); vi:=Imag;
    t:=tr*tr+ti*ti;
    IF t=0 THEN ErroFatal('Singular circuit for s='+Sre(sr,4,1)+' '+Sre(si,4,1)+'j'+fl+
      '  Use another freq. norm. factor if s is a pole');
    FOR j:=nos+1 DOWNTO i+1 DO BEGIN
      qr:=(Yr[i,j]*tr+Yi[i,j]*ti)/t;
      qi:=(Yi[i,j]*tr-Yr[i,j]*ti)/t;
      Yi[i,j]:=qi;
      Yr[i,j]:=qr;
      FOR k:=1 TO nos DO
        IF i<>k THEN BEGIN
          Yr[k,j]:=Yr[k,j]-Cmult(Yr[k,i],Yi[k,i],qr,qi);
          Yi[k,j]:=Yi[k,j]-Imag
        END
    END
  END;
END; {ResolverSistema}

FUNCTION Inverso(x:INTEGER):INTEGER;  {Bit inverso}
VAR
  i,u:INTEGER;
BEGIN
  u:=0;
  i:=graufft shr 1;
  REPEAT
    IF Odd(x) THEN u:=u+i;
    i:=i shr 1;
    x:=x shr 1
  UNTIL x=0;
  Inverso:=u
END; {Inverso}

PROCEDURE FFT;  {"Fast Fourier Transform"}
VAR
  k1,m,k,j,u,i:INTEGER;
  x1,y1,t:REAL;
BEGIN
  FOR k:=ordem-1 DOWNTO 0  DO BEGIN
    k1:=Round(Ex(2,k));
    m:=0;
    REPEAT
      j:=Inverso(m div k1);
      x1:=Cos(DoisPi*j/graufft); y1:=-Sin(DoisPi*j/graufft);
      FOR j:=0 TO k1-1 DO BEGIN
        u:=j+m; i:=u+k1;
        t:=Cmult(AA[i],BB[i],x1,y1);
        AA[u]:=AA[u]+t; BB[u]:=BB[u]+Imag;
        AA[i]:=AA[u]-t-t;
        BB[i]:=BB[u]-Imag-Imag
      END;
      m:=m+k1 shl 1
    UNTIL m>graufft-1
  END;
  FOR i:=0 TO graufft-1 DO BEGIN
    j:=Inverso(i);
    IF j>i THEN BEGIN
      x1:=AA[i]; AA[i]:=AA[j]; AA[j]:=x1
    END
  END;
  FOR i:=0 TO graufft-1 DO AA[i]:=AA[i]/graufft;
END; {FFT}

PROCEDURE AnunciarRaizes;
BEGIN
  IF numerador THEN txt:='Zeros: '
  ELSE txt:='Poles: ';
  txt:=txt+NomeAtual(atual)+', ';
  IF snorm^.sel_setting=2 THEN txt:=txt+'un';
  Saida(txt+'normalized');
END;

PROCEDURE ListarRaizes(n0:INTEGER; VAR Re,Im:raizes);
VAR
  i:INTEGER;
BEGIN
  FOR i:=1 TO n0 DO BEGIN
    IF Abs(Re[i])<tminimo^.panel_real THEN Re[i]:=0;
    IF Abs(Im[i])<tminimo^.panel_real THEN Im[i]:=0;
    txt:='x('+Sri(i)+')='+Cpct(fatord*Re[i]);
    IF Im[i]<>0 THEN BEGIN
      IF Im[i]>0 THEN txt:=txt+' ';
      txt:=txt+' '+Cpct(fatord*Im[i])+'j'
    END;
    Saida(txt)
  END
END;

PROCEDURE Biv(n0:INTEGER; a1:polinomio; VAR Re,Im:raizes; VAR raizes_validas:BOOLEAN);
CONST
  imax=50;
VAR
  a2,c1,c2:polinomio;
  tolm,t,tol,p1,p2,d,xr,xi,p,d1,d2,e1,e2:REAL;
  feito:BOOLEAN;
  i,j,nn,n,ordem:INTEGER;

BEGIN
  AnunciarRaizes;
  IF n0=0 THEN BEGIN Saida('No finite roots'); Exit END;
  tol:=ttol^.panel_real; tolm:=ttolm^.panel_real;
  xr:=treal^.panel_real; xi:=timag^.panel_real;
  feito:=FALSE; ordem:=0; nn:=0; n:=n0;
  FOR i:=0 TO n DO a2[i]:=0;
  {Elimina‡„o de ra¡zes na origem}
  WHILE (n>1) and (a1[0]=0) DO BEGIN
    Re[n]:=0; Im[n]:=0;
    n:=n-1;
    FOR i:=0 TO n DO a1[i]:=a1[i+1]
  END;
  WHILE NOT feito DO BEGIN
    IF n>1 THEN BEGIN
      {Calculo dos valores do polin“mio (p) e de sua derivada (d)}
      d1:=a1[n]; p1:=d1;
      d2:=a2[n]; p2:=d2;
      FOR i:=n-1 DOWNTO 0 DO BEGIN
        p1:=Cmult(p1,p2,xr,xi)+a1[i];
        p2:=Imag+a2[i];
        IF i>0 THEN BEGIN
          d1:=Cmult(d1,d2,xr,xi)+p1;
          d2:=Imag+p2;
        END
      END;
      {C lculo do erro. Esta forma dificulta overflow}
      IF (d1=0) or (d2=0) THEN BEGIN
        d:=Sqr(d1)+Sqr(d2);
        e1:=(p1*d1+p2*d2)/d;
        e2:=(p2*d1-p1*d2)/d
      END
      ELSE BEGIN
        d:=d1/d2+d2/d1;
        e1:=(p1/d2+p2/d1)/d;
        e2:=(p2/d2-p1/d1)/d
      END;
      {Testa poss¡vel ra¡z m£ltipla}
      d:=Abs(d1)+Abs(d2);
      p:=Abs(p1)+Abs(p2);
      IF (d<tolm) and (p<tolm) THEN BEGIN
        {deriva o polin“mio e continua}
        IF ordem=0 THEN BEGIN c1:=a1; c2:=a2 END;
        FOR i:=1 TO n DO BEGIN
          a1[i-1]:=a1[i]*i/n;
          a2[i-1]:=a2[i]*i/n;
        END;
        n:=n-1; ordem:=ordem+1;
      END
      ELSE BEGIN
        {Atualiza ra¡zes}
        xr:=xr-e1;
        xi:=xi-e2;
        {Testa convergˆncia}
        t:=Abs(e1)+Abs(e2);
        IF t<tol THEN BEGIN
          {Armazena ra¡zes calculadas}
          FOR i:=n+ordem DOWNTO n DO BEGIN
            Re[i]:=xr; Im[i]:=xi;
          END;
          {Rep”e polin“mio original, se for o caso}
          IF ordem>0 THEN BEGIN
            a1:=c1; a2:=c2; n:=n+ordem;
          END;
          {Deflaciona polin“mio}
          FOR i:=0 TO ordem DO BEGIN
            FOR j:=n-1 DOWNTO 1 DO BEGIN
              a1[j]:=Cmult(xr,xi,a1[j+1],a2[j+1])+a1[j];
              a2[j]:=Imag+a2[j];
            END;
            n:=n-1;
            FOR j:=0 TO n DO
              BEGIN a1[j]:=a1[j+1]; a2[j]:=a2[j+1] END
          END;
          {Prepara c lculo da pr¢xima ra¡z}
          IF (Abs(xi)>0.01) THEN xi:=-xi ELSE xi:=0.1;
          IF ordem>0 THEN xr:=xr-0.01; {evita derivada 0 a seguir}
          ordem:=0; nn:=0
        END
        ELSE BEGIN
          nn:=nn+1;
          {Demorando a convergir}
          IF nn>imax THEN BEGIN
            IF KeyPressed THEN BEGIN
              Saida('* Interrupted');
              Exit
            END;
            tol:=tol*10;
            Saida('*  Tolerance increased to '+Sre(tol,10,-1));
            nn:=0;
          END
        END
      END
    END
    ELSE BEGIN
      {Ultimas ra¡zes}
      d:=-(Sqr(a1[1])+Sqr(a2[1]));
      xr:=(a1[0]*a1[1]+a2[0]*a2[1])/d;
      xi:=(a2[0]*a1[1]-a1[0]*a2[1])/d;
      feito:=TRUE; nn:=0;
      FOR i:=n+ordem DOWNTO n DO BEGIN
        Re[i]:=xr; Im[i]:=xi;
      END
    END
  END;
  raizes_validas:=TRUE;
  ListarRaizes(n0,Re,Im)
END; {Biv}

PROCEDURE Lib(n0:INTEGER; A:polinomio; VAR Re,Im:raizes; VAR raizes_validas:BOOLEAN);
CONST
  imax=100;
VAR
  n,nraizes,i,j:INTEGER;
  t,u,v,u1,v1,c1,c2,c3,d,t1:REAL;
  B:polinomio;
LABEL Fim;

  PROCEDURE Resolve; {Calcula raizes de termo de 2o. grau}
  BEGIN
    d:=u*u-4*v;
    IF d>=0 THEN BEGIN
      Re[n]:=(-u+Sqrt(d))/2;
      Re[n-1]:=(-u-Sqrt(d))/2;
      Im[n]:=0; Im[n-1]:=0
    END
    ELSE BEGIN
      Re[n]:=-u/2; Re[n-1]:=-u/2;
      Im[n]:=Sqrt(-d)/2; Im[n-1]:=-Im[n]
    END;
    n:=n-2;
  END; {Resolve}

BEGIN
  AnunciarRaizes;
  IF n0=0 THEN BEGIN Saida('No finite roots'); Exit END;
  n:=n0;
  t:=ttol^.panel_real;
  v:=Sqr(treal^.panel_real)+Sqr(timag^.panel_real);
  u:=-2*treal^.panel_real;
  WHILE (A[0]=0) and (n>1) DO BEGIN
    Re[n]:=0; Im[n]:=0;
    Dec(n);
    For j:=0 TO n DO A[j]:=A[j+1]
  END;
  REPEAT
    IF n=1 THEN BEGIN
      Re[1]:=-A[0]/A[1]; Im[1]:=0;
      GoTo Fim
    END;
    IF n=2 THEN BEGIN
      u:=A[1]/A[2]; v:=A[0]/A[2];
      Resolve;
      GoTo Fim
    END;
    i:=0;
    REPEAT
      IF i>imax THEN BEGIN
        IF KeyPressed THEN BEGIN
          Saida('* Interrupted');
          Exit
         END;
        t:=t*10; i:=0;
        Saida('* Tolerance increased to '+Sre(t,10,-1));
      END;
      Inc(i);
      B[n]:=A[n]; c2:=B[n];
      B[n-1]:=A[n-1]-u*B[n];
      c1:=B[n-1]-u*c2;
      FOR j:=n-2 DOWNTO 1 DO BEGIN
        c3:=c2; c2:=c1;
        B[j]:=A[j]-u*B[j+1]-v*B[j+2];
        c1:=B[j]-u*c2-v*c3
      END;
      B[0]:=A[0]-u*B[1]-v*B[2];
      IF (c1<>0) and (c2<>0) and (c3<>0) THEN BEGIN
        u1:=(B[0]/c2-B[1]/c3)/(c2/c3-c1/c2);
        v1:=(B[1]/c2-B[0]/c1)/(c2/c1-c3/c2)
      END
      ELSE BEGIN
        d:=c2*c2-c1*c3;
        IF d=0 THEN BEGIN
          Saida('* Impossible to find roots');
          Exit
        END;
        u1:=(B[0]*c3-B[1]*c2)/d;
        v1:=(B[1]*c1-B[0]*c2)/d
      END;
      u:=u-u1; v:=v-v1;
      t1:=Abs(u1)+Abs(v1);
    UNTIL t1<t;
    Resolve;
    FOR j:=0 TO n DO A[j]:=B[j+2]
  UNTIL FALSE;
 Fim:raizes_validas:=TRUE;
  ListarRaizes(n0,Re,Im);
END; {Lib}

PROCEDURE ApresentarPolinomio(VAR grau:INTEGER; VAR cte:REAL; VAR Pol:polinomio;
                              VAR polinomio_valido,raizes_validas:BOOLEAN);
VAR
  maior,t,fw,fz,nively,dispersao:REAL;
  i,menorgrau,correcaoj:INTEGER;
  texto:STRING;
BEGIN
  polinomio_valido:=FALSE; raizes_validas:=FALSE;
  correcaoj:=0;
  IF numerador THEN BEGIN
    texto:='Numerator, node '+Sri(tsaida^.panel_int);
    IF tsaida^.panel_int>nosmesmo THEN BEGIN
      texto:=texto+' (current)';
      {Os numeradores dos j sao multiplicados por fatorz uma vez a mais}
      correcaoj:=1
    END;
    texto:=texto+', ';
    dispersao:=tdispnum^.panel_real;
    grau:=tngrau^.panel_int;
  END
  ELSE BEGIN
    texto:='Denominator, ';
    dispersao:=tdispden^.panel_real;
    grau:=tdgrau^.panel_int;
  END;
  IF not Normalizar THEN texto:=texto+'un';
  Saida(texto+'normalized');
  maior:=0;
  FOR i:=0 TO graufft-1 DO IF Abs(AA[i])>maior THEN maior:=Abs(AA[i]);
  IF maior=0 THEN BEGIN
    IF numerador THEN BEGIN
      Saida('Zero: no signal');
      Exit
    END
    ELSE BEGIN
      Saida('* Zero: bad impedance normalization');
      Exit
    END
  END;
  Pol:=AA;
  IF sforcar^.sel_setting=2 THEN BEGIN
    t:=maior/dispersao;
    FOR i:=0 TO graufft-1 DO IF Abs(Pol[i])>t THEN grau:=i ELSE Pol[i]:=0
  END;
  menorgrau:=0;
  WHILE (Pol[menorgrau]=0) and (menorgrau<grau) DO Inc(menorgrau);
  nively:=Pol[grau];
  IF nively=0 THEN BEGIN
    Saida('* The forced degree cannot be this');
    Exit
  END;
  FOR i:=0 TO grau DO BEGIN
    Pol[i]:=Pol[i]/nively;
    Saida('a('+Sri(i)+')='+Sre(Pol[i]*Ex(fatord,grau-i),20,-1));
  END;
  IF numerador THEN BEGIN
    cte:=nively/mden;
    IF correcaoj=1 THEN cte:=cte/fatorz;
    WITH funcao[0]^ DO Saida('Cst= '+Sre(cte*Ex(fatord,dgrau-ngrau),20,-1));
  END
  ELSE BEGIN
    mden:=nively;
    cte:=1
  END;
  IF grau>menorgrau THEN BEGIN
    fw:=tfatorw^.panel_real*Ex(Abs(Pol[menorgrau]),1/(grau-menorgrau));
    nively:=nively*Ex(tfatorw^.panel_real/fw,ind-grau)
  END
  ELSE fw:=0; {Haveria um valor ideal neste caso?}
  {Os elementos com girador introduzem 2 nos extra}
  i:=nos-2*(nosantes-nosmesmo)+correcaoj;
  IF i>0 THEN fz:=Ex(Abs(nively),-1/i)*fatorz ELSE fz:=0;
  IF numerador THEN BEGIN
    Saida('Used frequency normalization='+Cpct(tfatorw^.panel_real));
    Saida('Used impedance normalization='+Cpct(fatorz));
    IF fwd<>0 THEN Saida('Ideal f. n. for denominator= '+Cpct(fwd));
    IF fzd<>0 THEN BEGIN
      Saida('Ideal i. n. for denominator= '+Cpct(fzd));
      IF fwd=0 THEN Saida('(for the used f. n.)')
    END;
    IF fw<>0 THEN Saida('Ideal f. n. for numerator=   '+Cpct(fw));
    IF fz<>0 THEN BEGIN
      Saida('Ideal i. n. for numerator=   '+Cpct(fz));
      IF fw=0 THEN Saida('(for the used f. n.)')
    END;
  END
  ELSE BEGIN
    fwd:=fw;
    fzd:=fz;
    IF grau<>tdgrau^.panel_int THEN BEGIN
      Saida('* Complexity order differs from the expected ('+Sri(tdgrau^.panel_int)+')');
      Saida('  Verify analysis parameters (bad normalization?)');
      Exit
    END
  END;
  polinomio_valido:=TRUE;
END; {ApresentarPolinomio}

PROCEDURE AnalisarCircuito;
VAR
  i,ii,j:INTEGER;
BEGIN
  InvalidarAnalise(nil);
  graufft:=1;
  WHILE (graufft<=tdgrau^.panel_int) or (graufft<=tngrau^.panel_int) DO graufft:=graufft*2;
  IF graufft>Grmax+1 THEN ErroFatal('The maximum order is '+Sri(Grmax));
  ordem:=Round(Ln(graufft)/Ln(2));
  Saida('Order for the interpolation: '+Sri(graufft));
  ttysw_output(ttymsg,'Analyzing...');
  FOR ii:=0 TO graufft shr 1 DO BEGIN
    ang:=DoisPi*ii/graufft;
    sr:=tfatorw^.panel_real*Cos(ang);
    si:=tfatorw^.panel_real*Sin(ang);
    ttysw_output(ttymsg,Sri(graufft shr 1-ii)+' ');
    MontarSistema;
    {
    Saida(fl+'Sistema em '+Cpct(sr)+' '+Cpct(si));
    FOR i:=1 TO nos DO BEGIN
      FOR j:=1 TO nos+1 DO
        IF Yr[i,j]<>0 THEN ttysw_output(ttymsg,Sre(Yr[i,j],5,1))
        ELSE ttysw_output(ttymsg,'   . ');
      ttysw_output(ttymsg,fl)
    END;
    }
    ResolverSistema;
    Dr[ii]:=vr; Di[ii]:=vi;
    FOR i:=1 TO nos DO BEGIN
      Nr[i,ii]:=Cmult(Yr[i,nos+1],Yi[i,nos+1],vr,vi);
      Ni[i,ii]:=Imag
    END
  END;
  ttysw_output(ttymsg,fl);
  analise_feita:=TRUE;
END;

PROCEDURE CalcularDenominador;
VAR
  i,k:INTEGER;
BEGIN
  FOR i:=0 TO graufft shr 1 DO BEGIN
    k:=(graufft-i) mod graufft;
    AA[i]:=Dr[i]; AA[k]:=Dr[i];
    BB[i]:=Di[i]; BB[k]:=-Di[i]
  END;
  FFT;
  WITH funcao[0]^ DO
    ApresentarPolinomio(dgrau,cted,Den,denominador_valido,polos_validos);
END;

PROCEDURE CalcularNumerador;
VAR
  i,k:INTEGER;
BEGIN
  WITH funcao[0]^ DO BEGIN
    IF C[tsaida^.panel_int]=0 THEN BEGIN
      Saida('* Node '+Sri(tsaida^.panel_int)+' is real/virtual ground');
      numerador_valido:=FALSE
    END
    ELSE BEGIN
      FOR i:=0 TO graufft shr 1 DO BEGIN
        k:=(graufft-i) mod graufft;
        AA[i]:=Nr[C[tsaida^.panel_int],i]; AA[k]:=AA[i];
        BB[i]:=Ni[C[tsaida^.panel_int],i]; BB[k]:=-BB[i]
      END;
      FFT;
      ApresentarPolinomio(ngrau,cten,Num,numerador_valido,zeros_validos);
    END;
    nome:=rede+' n'+Sri(tsaida^.panel_int);
    IF not numerador_valido THEN BEGIN ngrau:=0; cten:=0 END
  END
END;

PROCEDURE SalvarPolinomio(nome:STRING; grau:INTEGER; cte,fator:REAL; VAR pol:polinomio);
VAR
  i:INTEGER;
BEGIN
  Assign(arquivo,nome);
  ReWrite(arquivo);
  WriteLn(arquivo,grau);
  FOR i:=0 TO grau DO WriteLn(arquivo,pol[i]);
  WriteLn(arquivo,cte);
  WriteLn(arquivo,fator);
  Close(arquivo);
  Saida('Normalized polynomial saved in file '+nome)
END;

PROCEDURE SalvarRaizes(nome:STRING; grau:INTEGER; cte,fator:REAL; VAR Re,Im:raizes);
VAR
  i:INTEGER;
BEGIN
  Assign(arquivo,nome);
  ReWrite(arquivo);
  WriteLn(arquivo,grau);
  FOR i:=1 TO grau DO WriteLn(arquivo,Re[i],' ',Im[i]);
  WriteLn(arquivo,cte);
  WriteLn(arquivo,fator);
  Close(arquivo);
  Saida('Normalized roots saved in file '+nome);
END;

FUNCTION AbrirArquivo(nome:STRING):BOOLEAN;
BEGIN
  AbrirArquivo:=FALSE;
  IF nome<>'' THEN BEGIN
    Assign(arquivo,nome);
    {$I-}
    Reset(arquivo);
    {$I+}
    IF IOResult=0 THEN AbrirArquivo:=TRUE
    ELSE Saida('* File '+nome+' not found')
  END
END;

PROCEDURE LerFinal(VAR cte,fator:REAL);
BEGIN
  IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte) ELSE cte:=1;
  IF not SeekEof(arquivo) THEN ReadLn(arquivo,fator) ELSE fator:=1;
  Saida('Cst='+Sre(cte,20,-1)+fl+'Norm. factor='+Sre(fator,20,-1));
  Close(arquivo)
END;

FUNCTION LerPolinomio(nome:STRING; VAR grau:INTEGER; VAR cte,fator:REAL; VAR pol:polinomio):BOOLEAN;
VAR
  i:INTEGER;
BEGIN
  IF AbrirArquivo(nome) THEN BEGIN
    Saida('Reading polynomial from file '+nome);
    ReadLn(arquivo,grau);
    Saida('Degree: '+Sri(grau));
    FOR i:=0 TO grau DO BEGIN
      ReadLn(arquivo,pol[i]);
      Saida('a('+Sri(i)+')='+Sre(pol[i],20,-1))
    END;
    LerFinal(cte,fator);
    LerPolinomio:=TRUE
  END
  ELSE LerPolinomio:=FALSE
END;

FUNCTION LerRaizes(nome:STRING; VAR grau:INTEGER; VAR cte,fator:REAL; VAR Re,Im:raizes):BOOLEAN;
VAR
  i:INTEGER;
BEGIN
  IF AbrirArquivo(nome) THEN BEGIN
    Saida('Reading roots from file '+nome);
    ReadLn(arquivo,grau);
    FOR i:=1 TO grau DO BEGIN
      ReadLn(arquivo,Re[i],Im[i]);
      Saida('x('+Sri(i)+')='+Sre(Re[i],20,-1));
      IF Im[i]<>0 THEN
        Saida('     '+Sre(Im[i],20,-1)+'j')
    END;
    LerFinal(cte,fator);
    LerRaizes:=TRUE
  END
  ELSE LerRaizes:=FALSE
END;

FUNCTION AlocarReferencia:BOOLEAN;
BEGIN
  IF (MaxAvail>SizeOf(fdet)) and (nref<maxref) THEN BEGIN
    Inc(nref);
    New(funcao[nref]);
    Saida('Reference #'+Sri(nref)+' created');
    AlocarReferencia:=TRUE
  END
  ELSE BEGIN
    Saida('* Too much references or insufficient memory');
    AlocarReferencia:=FALSE
  END
END;

PROCEDURE DesalocarReferencia;
BEGIN
  IF nref>0 THEN BEGIN
    Saida('Reference #'+Sri(nref)+' eliminated');
    Dispose(funcao[nref]);
    Dec(nref);
    atual:=0
  END
  ELSE Saida('* No references stored');
END;

PROCEDURE CalcularPolosEZeros;
BEGIN
  WITH funcao[atual]^ DO BEGIN
    IF Normalizar THEN fatord:=1 ELSE fatord:=fator;
    IF denominador_valido THEN BEGIN
      numerador:=FALSE;
      IF not polos_validos THEN
        IF smetodo^.sel_setting=2 THEN Biv(dgrau,Den,RePolos,ImPolos,polos_validos)
        ELSE Lib(dgrau,Den,RePolos,ImPolos,polos_validos)
    END
    ELSE Saida('* No denominator computed');
    IF numerador_valido THEN BEGIN
      numerador:=TRUE;
      IF not zeros_validos THEN
        IF smetodo^.sel_setting=2 THEN Biv(ngrau,Num,ReZeros,ImZeros,zeros_validos)
        ELSE Lib(ngrau,Num,ReZeros,ImZeros,zeros_validos)
    END
    ELSE Saida('* No numerator computed')
  END
END;

PROCEDURE ZoomOut;
BEGIN
  twmin^.panel_real:=wmin0;
  twmax^.panel_real:=wmax0;
  tgmin^.panel_real:=gmin0;
  tgmax^.panel_real:=gmax0
END;

{$F+}

PROCEDURE PrepararAnalise(obj:Xv_opaque);
BEGIN
  IF netlist_lido THEN open_window(jparametros)
  ELSE Saida('* No netlist read');
END;

PROCEDURE IniciarAnalise(obj:Xv_opaque);
VAR
  i,ii,k:INTEGER;
BEGIN
  close_window(jparametros);
  fatorz:=tfatorz^.panel_real;
  IF Normalizar THEN fatord:=1 ELSE fatord:=tfatorw^.panel_real;
  funcao[0]^.fator:=tfatorw^.panel_real;
  IF not analise_feita THEN AnalisarCircuito;
  ApagarTela;
  WITH funcao[0]^ DO BEGIN
    atual:=0;
    numerador:=FALSE;
    IF not denominador_valido THEN CalcularDenominador;
    IF denominador_valido THEN BEGIN
      numerador:=TRUE;
      IF not numerador_valido THEN CalcularNumerador;
      IF sraizes^.sel_setting=1 THEN CalcularPolosEZeros;
      IF numerador_valido and not jpfrequencia^.mapped THEN open_window(jpfrequencia)
    END
  END
END;

PROCEDURE InvalidarNumerador(obj:Xv_opaque);
BEGIN
  WITH funcao[0]^ DO BEGIN
    numerador_valido:=FALSE;
    zeros_validos:=FALSE;
    nome:=''
  END;
  raizes_plotadas:=FALSE;
  resposta_plotada:=FALSE
END;

PROCEDURE InvalidarDenominador(obj:Xv_opaque);
BEGIN
  WITH funcao[0]^ DO BEGIN
    denominador_valido:=FALSE;
    polos_validos:=FALSE;
  END;
  InvalidarNumerador(obj)
END;

PROCEDURE InvalidarRaizes(obj:Xv_opaque);
VAR
  i:INTEGER;
BEGIN
  WITH funcao[0]^ DO BEGIN
    polos_validos:=FALSE;
    zeros_validos:=FALSE;
  END;
  raizes_plotadas:=FALSE
END;

PROCEDURE InvalidarAnalise(obj:Xv_opaque);
BEGIN
  analise_feita:=FALSE;
  InvalidarDenominador(obj)
END;

PROCEDURE MudarElemento(obj:Xv_opaque);
VAR
  i:INTEGER;
BEGIN
  IF obj=bmais THEN Inc(eedit) ELSE Dec(eedit);
  IF eedit>numero THEN eedit:=1
  ELSE IF eedit<1 THEN eedit:=numero;
  WITH netlist[eedit] DO WITH biblioteca[tipo] DO BEGIN
     xv_set(tenome,nome);
     FOR i:=1 TO 4 DO
       IF i<=nval THEN BEGIN
         tvalor[i]^.panel_real:=val[i];
         xv_set(tvalor[i],nmval[i])
       END
       ELSE BEGIN
         tvalor[i]^.panel_real:=0;
         xv_set(tvalor[i],'-')
       END
  END;
END;

PROCEDURE AlterarValor(obj:Xv_opaque);
VAR
  i:INTEGER;
BEGIN
IF eedit>0 THEN WITH netlist[eedit] DO WITH biblioteca[tipo] DO
  FOR i:=1 TO 4 DO IF obj=tvalor[i] THEN BEGIN
    val[i]:=tvalor[i]^.panel_real;
    InvalidarAnalise(obj)
  END;
  open_window(jparametros)
END;

PROCEDURE AbrirNetList(obj:Xv_opaque);
BEGIN
  WITH tnetlist^ DO BEGIN
    IF Pos('.',panel_value)=0 THEN panel_value:=panel_value+'.net';
    rede:=Copy(panel_value,1,Pos('.',panel_value)-1);
    IF AbrirArquivo(panel_value) THEN BEGIN
      LerNetList;
      close_window(jdiretorio);
      PrepararAnalise(obj);
    END
  END
END; {AbrirNetList}

PROCEDURE TracarEscalas;
VAR
  i,j:INTEGER;
BEGIN
  SetTextStyle(SmallFont,HorizDir,4);
  Bar(0,0,xmin-1,ymax);
  i:=xmin-TextWidth('xxx');
  j:=(ymax+ymin) div 2-4;
  IF Teste(splotar,4) THEN BEGIN
    SetColor(cor[1]);
    Str(tamax^.panel_real:7:2,txt);
    OutTextXY(xmin-TextWidth(txt),ymin+16,txt);
    Str(tamin^.panel_real:7:2,txt);
    OutTextXY(xmin-TextWidth(txt),ymax-25,txt);
    OutTextXY(i,j-8,'s');
  END;
  IF Teste(splotar,2) THEN BEGIN
    SetColor(cor[2]);
    Str(tfmax^.panel_real:7:2,txt);
    OutTextXY(xmin-TextWidth(txt),ymin+8,txt);
    Str(tfmin^.panel_real:7:2,txt);
    OutTextXY(xmin-TextWidth(txt),ymax-17,txt);
    OutTextXY(i,j+8,'dg');
  END;
  SetColor(cor[0]);
  Str(tgmax^.panel_real:7:2,txt);
  OutTextXY(xmin-TextWidth(txt),ymin,txt);
  Str(tgmin^.panel_real:7:2,txt);
  OutTextXY(xmin-TextWidth(txt),ymax-9,txt);
  OutTextXY(i,j,'dB');
  SetColor(cor[0]);
  Bar(0,ymax+1,cresposta^.dx,cresposta^.dy);;
  OutTextXY(xmin,ymax,Sre(twmin^.panel_real,11,-1));
  Str(twmax^.panel_real:11,txt);
  OutTextXY(xmax-TextWidth(txt),ymax,txt);
  OutTextXY((xmax+xmin-TextWidth(unid[Rads])) div 2,ymax,unid[Rads]);
END;

FUNCTION Limita(a,b,y:REAL):INTEGER;
BEGIN
  y:=a*y+b;
  IF y<ymin THEN Limita:=ymin
  ELSE IF y>ymax THEN Limita:=ymax
    ELSE Limita:=Round(y)
END;

PROCEDURE PlotarRespostaEmFrequencia(obj:Xv_opaque);
VAR
  i,j,k:INTEGER;
  cte:REAL;
LABEL Fim;

  FUNCTION Cdiv(a1,a2,b1,b2:REAL):REAL;
  VAR
    t:REAL;
  BEGIN
    IF (b1=0) or (b2=0) THEN BEGIN
      t:=1/(Sqr(b1)+Sqr(b2));
      Cdiv:=(a1*b1+a2*b2)*t; Imag:=(a2*b1-a1*b2)*t
    END
    ELSE BEGIN
      t:=1/(b1/b2+b2/b1);
      Cdiv:=(a1/b2+a2/b1)*t; Imag:=(a2/b2-a1/b1)*t
    END;
  END;

BEGIN
  WITH funcao[0]^ DO IF not (numerador_valido and denominador_valido) THEN Exit;
  IF active_w<>jfrequencia THEN BEGIN {Por via das duvidas, pois nunca acontece}
    open_window(jfrequencia);
    Exit
  END;
  IF not resposta_plotada THEN ultpt:=-1;
  xv_set(jfrequencia,'Frequency Response');
  xmin:=TextWidth('-xxx.xx'); xmax:=obj^.dx-4; ymin:=3; ymax:=obj^.dy-TextHeight('X')-3;
  xq:=xmin+8; yq:=ymax-49;
  IF (twmin^.panel_real<=0) or (twmax^.panel_real<=0) THEN slog^.sel_setting:=2;
  IF Log THEN BEGIN
    dx:=Ex(twmax^.panel_real/twmin^.panel_real,1/tsegmentos^.panel_int);
    aw:=(xmax-xmin)/Ln(twmax^.panel_real/twmin^.panel_real);
    bw:=xmax-aw*Ln(twmax^.panel_real)
  END
  ELSE BEGIN
    dx:=(twmax^.panel_real-twmin^.panel_real)/tsegmentos^.panel_int;
    aw:=(xmax-xmin)/(twmax^.panel_real-twmin^.panel_real);
    bw:=xmax-aw*twmax^.panel_real
  END;
  ah:=(xmax-xmin)/tsegmentos^.panel_int;
  bh:=xmin;
  csr:=0;
  ag:=(ymax-ymin)/(tgmin^.panel_real-tgmax^.panel_real);
  bg:=ymax-ag*tgmin^.panel_real;
  af:=(ymax-ymin)/(tfmin^.panel_real-tfmax^.panel_real);
  bf:=ymax-af*tfmin^.panel_real;
  at:=(ymax-ymin)/(tamin^.panel_real-tamax^.panel_real);
  bt:=ymax-at*tamin^.panel_real;
  IF (twmax^.panel_real<twmin^.panel_real) or (tgmax^.panel_real<tgmin^.panel_real) THEN
    splotar^.sel_setting:=splotar^.sel_setting and (not 1);
  SetFillStyle(SolidFill,obj^.back_color);
  Bar(0,0,obj^.dx,obj^.dy);
  IF Teste(splotar,1) THEN BEGIN
    SetLineStyle(DottedLn,0,NormWidth);
    SetColor(cor[cor_fraca]);
    IF (twmax^.panel_real-twmin^.panel_real>twmin^.panel_real) and Log THEN t1:=twmin^.panel_real
    ELSE t1:=twmax^.panel_real-twmin^.panel_real;
    t1:=Ex(10,Round(Ln(t1)/Ln(10)-0.499999));
    t2:=Round(twmin^.panel_real/t1+0.5)*t1;
    WHILE t2<twmax^.panel_real DO
      IF Log THEN BEGIN
        IF Round(t2/t1)=10 THEN BEGIN
          t1:=10*t1;
          SetColor(cor[1]);
        END;
        i:=Round(aw*Ln(t2)+bw);
        Line(i,ymin,i,ymax);
        t2:=t2+t1;
        SetColor(cor[cor_fraca]);
      END
      ELSE BEGIN
        i:=Round(aw*t2+bw);
        Line(i,ymin,i,ymax);
        t2:=t2+t1
      END;
    t1:=tgmax^.panel_real-tgmin^.panel_real;
    t1:=Ex(10,Round(Ln(t1)/Ln(10)-0.5));
    t2:=Round(tgmin^.panel_real/t1+0.5)*t1;
    WHILE t2<tgmax^.panel_real DO BEGIN
      i:=Limita(ag,bg,t2);
      Line(xmin,i,xmax,i);
      t2:=t2+t1
    END
  END;
  SetLineStyle(SolidLn,0,NormWidth);
  SetColor(cor[0]);
  Rectangle(xmin,ymin,xmax,ymax);
  ResetSprite(1);
  TracarEscalas;
  f:=twmin^.panel_real; ix:=0;
  REPEAT
    IF ix>ultpt THEN BEGIN
      FOR i:=0 TO nref DO
        WITH funcao[i]^ DO BEGIN
          cte:=cten/cted;
          IF Normalizar THEN fatord:=1 ELSE fatord:=fator;
          IF Rads THEN w:=f/fatord ELSE w:=DoisPi*f/fatord;
          b1:=0; b2:=0; db1:=0; db2:=0;
          FOR j:=dgrau DOWNTO 0 DO
             BEGIN t:=b1*w; b1:=Den[j]-w*b2; b2:=t END;
          FOR j:=dgrau DOWNTO 1 DO
             BEGIN t:=db1*w; db1:=j*Den[j]-w*db2; db2:=t END;
          a1:=0; a2:=0; da1:=0; da2:=0;
          FOR j:=ngrau DOWNTO 0 DO
            BEGIN t:=a1*w; a1:=Num[j]-w*a2; a2:=t END;
          FOR j:=ngrau DOWNTO 1 DO
             BEGIN t:=da1*w; da1:=j*Num[j]-w*da2; da2:=t END;
          sr:=cte*Cdiv(a1,a2,b1,b2);
          si:=cte*Imag;
          IF sr=0 THEN BEGIN
            IF si=0 THEN si:=1e-11;
            sr:=si*1.e-11
          END;
          Fas[ix]:=Arctan(si/sr)*RadGraus;
          Gan[ix]:=Ln(Sqr(sr)+Sqr(si))*LnDb;
          Tg[ix]:=(Cdiv(db1,db2,b1,b2)-Cdiv(da1,da2,a1,a2))/fatord;
          IF sr<0 THEN
            IF si>0 THEN Fas[ix]:=180+Fas[ix] ELSE Fas[ix]:=Fas[ix]-180;
        END;
      Frq[ix]:=f
    END;
    j:=Round(ix*ah+bh);
    FOR i:=nref DOWNTO 0 DO WITH funcao[i]^ DO BEGIN
      IF modo1 THEN SetColor(cor[0]) ELSE SetColor(cor[i]);
      k:=Limita(ag,bg,Gan[ix]);
      IF ix>0 THEN Line(xa,ga,j,k);
      ga:=k;
      IF Teste(splotar,2) THEN BEGIN
        IF modo1 THEN SetColor(cor[2]) ELSE SetColor(cor[i]);
        k:=Limita(af,bf,Fas[ix]);
        IF ix>0 THEN Line(xa,fa,j,k);
        fa:=k
      END;
      IF Teste(splotar,4) THEN BEGIN
        IF modo1 THEN SetColor(cor[1]) ELSE SetColor(cor[i]);
        k:=Limita(at,bt,Tg[ix]);
        IF ix>0 THEN Line(xa,ta,j,k);
        ta:=k
      END;
    END;
    xa:=j;
    IF KeyPressed THEN BEGIN
      IF ix>ultpt THEN ultpt:=ix;
      GoTo Fim;
    END;
    IF Log THEN f:=f*dx ELSE f:=f+dx;
    Inc(ix)
  UNTIL ix>tsegmentos^.panel_int;
  ix:=tsegmentos^.panel_int; ultpt:=ix;
 Fim:resposta_plotada:=TRUE;
END;

PROCEDURE EventosResposta(obj:Xv_opaque);
CONST
  xi:INTEGER=0;
  yi:INTEGER=0;
  xf:INTEGER=0;
  yf:INTEGER=0;
  selecao:BOOLEAN=FALSE;

  PROCEDURE Cursor;
  BEGIN
    WITH funcao[atual]^ DO BEGIN
      PutSprite(Round(ah*csr+bh),Limita(ag,bg,Gan[csr]),1);
      SetColor(cor[1]);
      SetFillStyle(emptyfill,obj^.back_color);
      SetTextStyle(SmallFont,HorizDir,4);
      Bar(xq-1,yq+1,xq+106,yq+43);
      Rectangle(xq-2,yq,xq+107,yq+44);
      SetColor(cor[0]);
      OutTextXY(xq,yq,NomeAtual(atual));
      OutTextXY(xq,yq+8,Sre(Frq[csr],12,-1)+' '+unid[Rads]);
      OutTextXY(xq,yq+16,Sre(Gan[csr],13,8)+' dB');
      OutTextXY(xq,yq+24,Sre(Fas[csr],13,8)+' dg');
      OutTextXY(xq,yq+32,Sre(Tg[csr],13,8)+' s')
    END;
  END;

BEGIN
  IF not resposta_plotada THEN Exit;
  IF ie_code<256 THEN CASE UpCase(Chr(ie_code)) OF
    #0:CASE ReadKey OF
         'K':BEGIN IF csr>=1 THEN Dec(csr); Cursor; Exit END;
          #115:BEGIN IF csr>=10 THEN Dec(csr,10); Cursor; Exit END;
          'M':BEGIN IF csr<=ix-1 THEN Inc(csr); Cursor; Exit END;
          #116:BEGIN IF csr<=ix-10 THEN Inc(csr,10); Cursor; Exit END;
          'H':BEGIN
                t:=(tgmax^.panel_real-tgmin^.panel_real)/2;
                tgmin^.panel_real:=tgmin^.panel_real+t;
                tgmax^.panel_real:=tgmax^.panel_real+t;
              END;
          'P':BEGIN
                t:=(tgmax^.panel_real-tgmin^.panel_real)/2;
                tgmin^.panel_real:=tgmin^.panel_real-t;
                tgmax^.panel_real:=tgmax^.panel_real-t;
              END
          ELSE Exit;
        END;
     '-':tgmax^.panel_real:=2*tgmax^.panel_real-tgmin^.panel_real;
     '+':tgmax^.panel_real:=(tgmax^.panel_real+tgmin^.panel_real)/2;
      #9:BEGIN IF atual<nref THEN Inc(atual) ELSE atual:=0; Cursor; Exit END;
      #8:BEGIN IF atual>0 THEN Dec(atual) ELSE atual:=nref; Cursor; Exit END;
     'G':Inverter(splotar,1);
     'F':Inverter(splotar,2);
     'T':Inverter(splotar,4);
     'L':WITH slog^ DO BEGIN IF Log THEN sel_setting:=2 ELSE sel_setting:=1; resposta_plotada:=FALSE END;
     'R':BEGIN
           IF Log THEN twmax^.panel_real:=twmin^.panel_real*Sqr(twmax^.panel_real/twmin^.panel_real)
           ELSE twmax^.panel_real:=twmin^.panel_real+(twmax^.panel_real-twmin^.panel_real)*2;
           resposta_plotada:=FALSE
         END;
     'A':BEGIN
           IF Log THEN twmax^.panel_real:=twmin^.panel_real*Sqrt(twmax^.panel_real/twmin^.panel_real)
           ELSE twmax^.panel_real:=twmin^.panel_real+(twmax^.panel_real-twmin^.panel_real)/2;
           resposta_plotada:=FALSE
         END;
     '>','.':BEGIN
           IF Log THEN BEGIN
             t:=Sqrt(Sqrt(twmax^.panel_real/twmin^.panel_real));
             twmin^.panel_real:=twmin^.panel_real*t;
             twmax^.panel_real:=twmax^.panel_real*t
           END
           ELSE BEGIN
             t:=(twmax^.panel_real-twmin^.panel_real)/4;
             twmin^.panel_real:=twmin^.panel_real+t;
             twmax^.panel_real:=twmax^.panel_real+t
           END;
           resposta_plotada:=FALSE
         END;
    '<',',':BEGIN
          IF Log THEN BEGIN
            t:=Sqrt(Sqrt(twmax^.panel_real/twmin^.panel_real));
            twmin^.panel_real:=twmin^.panel_real/t;
            twmax^.panel_real:=twmax^.panel_real/t
          END
          ELSE BEGIN
            t:=(twmax^.panel_real-twmin^.panel_real)/4;
            twmin^.panel_real:=twmin^.panel_real-t;
            twmax^.panel_real:=twmax^.panel_real-t
          END;
          resposta_plotada:=FALSE
        END;
    'C':modo1:=not modo1;
    'Z':BEGIN ZoomOut; resposta_plotada:=FALSE END
    ELSE Exit
  END
  ELSE IF ie_shiftcode=4 THEN BEGIN
    csr:=Round((ie_locx-bh)/ah);
    IF csr<0 THEN csr:=0;
    IF csr>ix THEN csr:=ix;
    Cursor;
    Exit
  END
  ELSE IF selecao THEN BEGIN
    SetWriteMode(XorPut);
    SetColor(white);
    IF ie_code=LOC_DRAG THEN BEGIN
      Rectangle(xi,yi,xf,yf);
      xf:=ie_locx; yf:=ie_locy;
      Rectangle(xi,yi,xf,yf);
      Exit
    END;
    IF ie_shiftcode=0 THEN BEGIN
      selecao:=FALSE;
      Rectangle(xi,yi,xf,yf);
      IF (xi<>xf) and (yi<>yf) THEN BEGIN
        resposta_plotada:=FALSE;
        WITH twmin^ DO BEGIN
          panel_real:=(xi-bw)/aw;
          IF Log THEN panel_real:=exp(panel_real)
        END;
        WITH twmax^ DO BEGIN
          panel_real:=(xf-bw)/aw;
          IF Log THEN panel_real:=exp(panel_real)
        END;
        tgmin^.panel_real:=(yf-bg)/ag;
        tgmax^.panel_real:=(yi-bg)/ag
      END
      ELSE Exit
    END;
    SetWriteMode(NormalPut);
  END
  ELSE IF (ie_code=MS_LEFT) THEN BEGIN
    xi:=ie_locx; yi:=ie_locy;
    xf:=xi; yf:=yi;
    selecao:=TRUE;
    Exit
  END
  ELSE Exit;
  PlotarRespostaEmFrequencia(cresposta);
END;

FUNCTION LimX(x:REAL):INTEGER;
VAR
  t:REAL;
BEGIN
  t:=ax*x+bx;
  IF t>xpmax THEN LimX:=xpmax
  ELSE IF t<0 THEN LimX:=0
    ELSE LimX:=Round(t)
END;

FUNCTION LimY(y:REAL):INTEGER;
VAR
  r:REAL;
BEGIN
  t:=ay*y+by;
  IF t>ypmax THEN LimY:=ypmax
  ELSE IF t<0 THEN LimY:=0
    ELSE LimY:=Round(t)
END;

PROCEDURE PlotarPolosEZeros(obj:Xv_opaque);
VAR
  i:INTEGER;
  xa,ya:WORD;

  PROCEDURE Plotar(grau:INTEGER; VAR Re,Im:raizes; polo:BOOLEAN);
  VAR
    i,x,y:INTEGER;
  BEGIN
    FOR i:=1 TO grau DO BEGIN
      x:=LimX(Re[i]*fatord);
      y:=LimY(Im[i]*fatord);
      IF polo THEN BEGIN
        Line(x-2,y-2,x+2,y+2);
        Line(x-2,y+2,x+2,y-2)
      END
      ELSE Circle(x,y,4)
    END;
  END;

BEGIN
  WITH funcao[atual]^ DO IF not (zeros_validos or polos_validos) THEN Exit;
  IF active_w<>jraizes THEN BEGIN
    {Usa o fator de normalizacao para setar a escala inicial}
    IF Normalizar THEN remin:=-2 ELSE remin:=-tfatorw^.panel_real*2;
    immin:=remin;
    delta:=-2*immin;
    {Assim se garante que a rotina nao chamara a si propria na abertura}
    craizes^.notify_handler:=Nothing;
    open_window(jraizes);
    craizes^.notify_handler:=PlotarPolosEZeros;
    IF not xv_ok THEN Exit
  END;
  ResetSprite(2);
  WITH craizes^ DO BEGIN
    SetFillStyle(SolidFill,back_color);
    Bar(0,0,dx,dy);
    SetTextStyle(SmallFont,HorizDir,4);
    ypmax:=dy-11;
    GetAspectRatio(xa,ya);
    xpmax:=Trunc(ypmax*ya/xa);
    IF xpmax>dx-90 THEN BEGIN
      xpmax:=dx-90;
      ypmax:=Trunc(xpmax*xa/ya)
    END;
    basex:=xpmax+2;
    basey:=24;
    ay:=-ypmax/delta; by:=ypmax-ay*immin;
    ax:=xpmax/delta; bx:=-ax*remin;
    SetLineStyle(DottedLn,0,NormWidth);
    SetColor(cor[cor_fraca]);
    i:=LimX(0);
    Line(i,0,i,ypmax);
    i:=LimY(0);
    Line(0,i,xpmax,i);
    SetColor(fore_color);
    OutTextXY(0,ypmax,Sre(remin,10,-1));
    Str(remin+delta:10,txt);
    OutTextXY(xpmax-TextWidth(txt),ypmax,txt);
    OutTextXY(basex,ypmax-9,Sre(immin,10,-1));
    OutTextXY(basex,0,Sre(immin+delta,10,-1));
    SetLineStyle(SolidLn,0,NormWidth);
    Rectangle(0,0,xpmax,ypmax);
    FOR i:=nref DOWNTO 0 DO WITH funcao[i]^ DO BEGIN
      SetColor(cor[i]);
      IF Normalizar THEN fatord:=1 ELSE fatord:=fator;
      IF polos_validos THEN Plotar(dgrau,RePolos,ImPolos,TRUE);
      IF zeros_validos THEN Plotar(ngrau,ReZeros,ImZeros,FALSE);
    END
  END;
  raizes_plotadas:=TRUE
END;

PROCEDURE EventosPolosEZeros(obj:Xv_opaque);
CONST
  xi:INTEGER=0;
  yi:INTEGER=0;
  xf:INTEGER=0;
  yf:INTEGER=0;
  selecao:BOOLEAN=FALSE;

VAR
  x,y,x1,y1,dist:REAL;
  i:INTEGER;

  PROCEDURE Testar(i,n:INTEGER; VAR Re,Im:raizes; saopolos:BOOLEAN);
  VAR
    teste:REAL;
    j:INTEGER;
  BEGIN
    FOR j:=1 TO n DO BEGIN
      teste:=Abs(x1-Re[j]*fatord)+Abs(y1-Im[j]*fatord);
      IF teste<dist THEN BEGIN
        atual:=i;
        dist:=teste;
        polos:=saopolos;
        x:=Re[j]*fatord;
        y:=Im[j]*fatord;
      END
    END
  END;

BEGIN
  IF not raizes_plotadas THEN Exit;
  IF ie_code<256 THEN
    CASE UpCase(Chr(ie_code)) OF
      #0:BEGIN
           CASE ReadKey OF
             'H':immin:=immin+delta/4;
             'P':immin:=immin-delta/4;
             'M':remin:=remin+delta/4;
             'K':remin:=remin-delta/4;
             ELSE Exit
           END
         END;
      '-':BEGIN
            immin:=immin-delta/2;
            remin:=remin-delta/2;
            delta:=delta*2
          END;
      '+':BEGIN
            immin:=immin+delta/4;
            remin:=remin+delta/4;
            delta:=delta/2;
          END
      ELSE Exit;
    END
    ELSE IF ie_shiftcode>1 THEN BEGIN
      SetTextStyle(SmallFont,HorizDir,4);
      x1:=(ie_locx-bx)/ax;
      y1:=(ie_locy-by)/ay;
      dist:=1e38;
      FOR i:=0 TO nref DO WITH funcao[i]^ DO BEGIN
        IF Normalizar THEN fatord:=1 ELSE fatord:=fator;
        IF polos_validos THEN Testar(i,dgrau,RePolos,ImPolos,TRUE);
        IF zeros_validos THEN Testar(i,ngrau,ReZeros,ImZeros,FALSE)
      END;
      WITH funcao[atual]^ DO BEGIN
        PutSprite(LimX(x),LimY(y),2)
      END;
      WITH craizes^ DO BEGIN
        SetFillStyle(SolidFill,back_color);
        Bar(basex,basey,dx,basey+49);
        SetColor(fore_color)
      END;
      OutTextXY(basex,basey,NomeAtual(atual));
      MoveTo(basex,basey+8);
      IF polos THEN OutText('Pole: ') ELSE OutText('Zero: ');
      OutTextXY(basex,basey+16,'Re:'+Sre(x,12,-1));
      OutTextXY(basex,basey+24,'Im:'+Sre(y,12,-1));
      w:=Sqrt(Sqr(x)+Sqr(y));
      OutTextXY(basex,basey+32,'w: '+Sre(w,12,-1));
      MoveTo(basex,basey+40); OutText('Q: ');
      IF Abs(x)>tminimo^.panel_real THEN OutText(Sre(-0.5*w/x,12,2))
      ELSE OutText(' infinite');
      Exit;
    END
    ELSE IF selecao THEN BEGIN
      SetWriteMode(XorPut);
      SetColor(white);
      IF ie_code=LOC_DRAG THEN BEGIN
        Rectangle(xi,yi,xf,yf);
        yf:=ie_locy;
        xf:=xi+Round((yi-yf)*ax/ay);
        Rectangle(xi,yi,xf,yf);
        Exit
      END;
      IF ie_shiftcode=0 THEN BEGIN
        selecao:=FALSE;
        Rectangle(xi,yi,xf,yf);
        IF (xi<>xf) and (yi<>yf) THEN BEGIN
           remin:=(xi-bx)/ax;
           immin:=(yf-by)/ay;
           delta:=(yi-yf)/ay;
        END
        ELSE Exit
      END;
      SetWriteMode(NormalPut);
    END
    ELSE IF (ie_code=MS_LEFT) THEN BEGIN
      xi:=ie_locx; yi:=ie_locy;
      xf:=xi; yf:=yi;
      selecao:=TRUE;
      Exit
    END
    ELSE Exit;
  PlotarPolosEZeros(craizes);
END;

PROCEDURE ZerarGrafico(obj:Xv_opaque);
BEGIN
  resposta_plotada:=FALSE;
END;

PROCEDURE IniciarResposta(obj:Xv_opaque);
BEGIN
  WITH funcao[0]^ DO
    IF not (denominador_valido and numerador_valido) THEN BEGIN
      Saida('* No response computed');
      Exit
    END;
  wmin0:=twmin^.panel_real;
  wmax0:=twmax^.panel_real;
  gmin0:=tgmin^.panel_real;
  gmax0:=tgmax^.panel_real;
  WHILE active_w<>jfrequencia DO close_window(active_w);
  PlotarRespostaEmFrequencia(cresposta);
  SetTextStyle(DefaultFont,HorizDir,1);
  IF sraizes^.sel_setting=1 THEN PlotarPolosEZeros(craizes);
END;

PROCEDURE SetarNome(obj:Xv_opaque);
BEGIN
  txt:=ttitulo^.panel_value;
  iii:=tnsaida^.panel_int;
  tnumerador^.panel_value:=txt+'.n'+Sri(iii);
  tdenominador^.panel_value:=txt+'.d';
  tzeros^.panel_value:=txt+'.z'+Sri(iii);
  tpolos^.panel_value:=txt+'.r';
  draw_object(jreferencia,TRUE);
END;

PROCEDURE LerReferencia(obj:Xv_opaque);
BEGIN
  ApagarTela;
  IF AlocarReferencia THEN
    WITH funcao[nref]^ DO BEGIN
      nome:=tnumerador^.panel_value;
      numerador_valido:=LerPolinomio(nome,ngrau,cten,fator,Num);
      denominador_valido:=LerPolinomio(tdenominador^.panel_value,dgrau,cted,fator,Den);
      zeros_validos:=LerRaizes(tzeros^.panel_value,ngrau,cten,fator,ReZeros,ImZeros);
      polos_validos:=LerRaizes(tpolos^.panel_value,dgrau,cted,fator,RePolos,ImPolos);
      IF numerador_valido and denominador_valido THEN BEGIN
        atual:=nref;
        resposta_plotada:=FALSE;
        raizes_plotadas:=FALSE;
        close_window(jreferencia);
      END
      ELSE BEGIN
        Saida('* Reference incomplete');
        DesalocarReferencia
      END
    END
END;

PROCEDURE TratarMenu1(obj:Xv_opaque);
VAR
  i:INTEGER;
BEGIN
  CASE obj^.sel_menu OF
    1:open_window(jdiretorio);
    2:open_window(jterminal);
    3:PrepararAnalise(obj);
    4:open_window(jpfrequencia);
    5:BEGIN
        FOR atual:=0 TO nref DO CalcularPolosEZeros;
        atual:=0;
        PlotarPolosEZeros(craizes)
      END;
    6:IF netlist_lido THEN open_window(jedit)
      ELSE Saida('* No netlist read');
    9:BEGIN
        ApagarTela;
        Saida('IFFT - version '+versao);
        Saida(precisao+' precision');
        Saida('Linear circuit analysis with FFT interpolation');
        Saida('By: Antonio Carlos Moreirao de Queiroz');
        Saida('COPPE - DEEL');
        Saida('Universidade Federal do Rio de Janeiro - 1992');
        Saida('e-mail: acmq@coe.ufrj.br');
        Saida('Total free memory:  '+Sri(MemAvail)+' bytes'+fl+
              'Largest free block: '+Sri(MaxAvail)+' bytes');
        Saida('Stored transfer functions: ');
        FOR i:=0 TO nref DO WITH funcao[i]^ DO BEGIN
          ttysw_output(ttymsg,NomeAtual(i)+' (');
          IF denominador_valido THEN ttysw_output(ttymsg,' den. ');
          IF numerador_valido THEN ttysw_output(ttymsg,' num. ');
          IF polos_validos THEN ttysw_output(ttymsg,' poles ');
          IF zeros_validos THEN ttysw_output(ttymsg,' zeros ');
          Saida(')')
        END
      END;
    10:Back;
    11:open_window(jextra);
    12:IF netlist_lido THEN open_window(jmontecarlo)
       ELSE Saida('* No netlist read');
    13:xv_end:=TRUE
  END
END;

PROCEDURE TratarMenu2(obj:Xv_opaque);
VAR
  i:WORD;
  dia,mes,ano,dsem,hora,minuto,segundo,seg100:WORD;
BEGIN
  WITH funcao[0]^ DO CASE obj^.sel_menu OF
    1:IF resposta_plotada THEN BEGIN
        txt:=rede+'.g'+Sri(tsaida^.panel_int);
        Assign(arquivo,txt);
        Rewrite(arquivo);
        GetDate(ano,mes,dia,dsem);
        GetTime(hora,minuto,segundo,seg100);
        WriteLn(arquivo,'IFFT - ',dia,'/',mes,'/',ano,' ',hora,':',minuto,':',segundo);
        WriteLn(arquivo,'Network: ',rede,'; Frequency response: Output ',tsaida^.panel_int);
        WriteLn(arquivo,'#','Freq.('+unid[Rads]+')':13,'Gain (dB)':15,'Phase (deg)':15,'Delay (s)':15);
        FOR i:=0 TO ultpt DO BEGIN
          Write(arquivo,Frq[i]:14:9);
          WriteLn(arquivo,' ',Gan[i]:14:9,' ',Fas[i]:14:9,' ',Tg[i]:14:9);
        END;
        WriteLn(arquivo);
        Close(arquivo);
        Saida('Table saved in file '+txt)
      END
      ELSE Saida('* No response computed');
    2:BEGIN
        IF denominador_valido THEN
          SalvarPolinomio(rede+'.d',dgrau,cted,fator,Den)
        ELSE Saida('* No denominator computed');
        IF numerador_valido THEN
          SalvarPolinomio(rede+'.n'+Sri(tsaida^.panel_int),ngrau,cten,fator,Num)
        ELSE Saida('* No numerator computed');
      END;
    3:BEGIN
        IF polos_validos THEN
          SalvarRaizes(rede+'.r',dgrau,cted,fator,RePolos,ImPolos)
        ELSE Saida('* No poles computed');
        IF zeros_validos THEN
          SalvarRaizes(rede+'.z'+Sri(tsaida^.panel_int),ngrau,cten,fator,ReZeros,ImZeros)
        ELSE Saida('* No zeros computed');
      END;
    4:BEGIN
        Assign(arquivo,rede+'.msg');
        ReWrite(arquivo);
        WITH ttymsg^ DO BEGIN
          i:=bstart;
          WHILE i<>tend DO BEGIN
            Write(arquivo,Pb^[i]);
            IF i<bsize THEN Inc(i) ELSE i:=0
          END
        END;
        Close(arquivo);
        Saida('Messages saved in file '+rede+'.msg')
      END
  END
END;

PROCEDURE TratarMenu3(obj:Xv_opaque);
VAR
  i,j,n:INTEGER;
BEGIN
  CASE obj^.sel_menu OF
    1:WITH funcao[0]^ DO
       IF denominador_valido or numerador_valido or polos_validos or zeros_validos THEN BEGIN
         IF AlocarReferencia THEN BEGIN
           funcao[nref]^:=funcao[0]^;
         END
       END
       ELSE Saida('* No function computed/read');
    2:DesalocarReferencia;
    3:IF nref>0 THEN
        WHILE nref>0 DO DesalocarReferencia
      ELSE Saida('* No references stored');
    4:open_window(jreferencia);
    5:BEGIN
        funcao[0]^:=funcao[nref]^;
        Saida('Reference #'+Sri(nref)+' restored');
        rede:='Ref'+Sri(nref);
        DesalocarReferencia
      END;
    6:IF (nref>0) THEN BEGIN
        IF (resposta_plotada) THEN BEGIN
          Assign(arquivo,rede+'.rfr');
          ReWrite(arquivo);
          FOR j:=1 TO nref DO WITH funcao[j]^ DO BEGIN
            WriteLn(arquivo,'# Frequency response - Ref #',j);
            FOR i:=0 TO ultpt DO
              WriteLn(arquivo,Frq[i]:14:9,' ',Gan[i]:14:9,' ',Fas[i]:14:9,' ',Tg[i]:14:9);
            WriteLn(arquivo)
          END;
          Close(arquivo);
          Saida(Sri(nref)+' responses saved in file '+rede+'.rfr')
        END;
        Assign(arquivo,rede+'.rpo');
        ReWrite(arquivo);
        n:=0;
        FOR j:=1 TO nref DO WITH funcao[j]^ DO IF polos_validos THEN BEGIN
          WriteLn(arquivo,'Poles - Ref #',j);
          FOR i:=1 TO dgrau DO WriteLn(arquivo,fator*RePolos[i],' ',fator*ImPolos[i]);
          WriteLn(arquivo);
          Inc(n)
        END;
        Close(arquivo);
        Saida(Sri(n)+' groups of poles saved in file '+rede+'.rpo');
        Assign(arquivo,rede+'.rze');
        ReWrite(arquivo);
        n:=0;
        FOR j:=1 TO nref DO WITH funcao[j]^ DO IF zeros_validos THEN BEGIN
          WriteLn(arquivo,'Zeros - Ref #',j);
          FOR i:=1 TO ngrau DO WriteLn(arquivo,fator*ReZeros[i],' ',fator*ImZeros[i]);
          WriteLn(arquivo);
          Inc(n)
        END;
        Close(arquivo);
        Saida(Sri(n)+' groups of zeros saved in file '+rede+'.rze');
      END
  END
END;

VAR
  nomes,total:INTEGER;

PROCEDURE LerDiretorio(obj:Xv_opaque);
VAR
  srec:SearchRec;

BEGIN
  SetTextStyle(smallfont,horizdir,4);
  IF obj<>cdiretorio THEN BEGIN
    SetFillStyle(SolidFill,cdiretorio^.back_color);
    Bar(0,0,cdiretorio^.dx,cdiretorio^.dy)
  END;
  nomes:=(cdiretorio^.dx) div 78;
  total:=0;
  FindFirst(tmask^.panel_value,AnyFile,srec);
  WHILE DosError=0 DO BEGIN
    OutTextXY(3+(total mod nomes)*78,(total div nomes)*8,srec.Name);
    FindNext(srec);
    Inc(total)
  END;
  Dec(total)
END;

PROCEDURE EscolherArquivo(obj:Xv_opaque);
VAR
  srec:SearchRec;
  D:DirStr;
  N:NameStr;
  E:ExtStr;
  i,k:INTEGER;

BEGIN
  IF ie_code=MS_LEFT THEN BEGIN
    k:=(ie_locx-3) div 78;
    IF k<nomes THEN BEGIN
      k:=k+((ie_locy-3) div 8)*nomes;
      IF k<=total THEN BEGIN
        i:=0;
        FindFirst(tmask^.panel_value,AnyFile,srec);
        WHILE (DosError=0) and (i<k) DO BEGIN
          FindNext(srec);
          Inc(i)
        END;
        FSplit(tmask^.panel_value,D,N,E);
        tnetlist^.panel_value:=D+srec.Name;
        xv_set(tnetlist,tnetlist^.xv_label);
        AbrirNetList(nil)
      END
    END
  END
END;

PROCEDURE ExecutarVarredura(obj:Xv_opaque);
VAR
  esweep,psweep:INTEGER;
  vmin,vmax,vsweep,voriginal,vstep:REAL;
  lin:BOOLEAN;
BEGIN
  esweep:=1;
  WHILE (esweep<=numero) and (netlist[esweep].nome<>tswel^.panel_value) DO Inc(esweep);
  IF (esweep<=numero) THEN  WITH netlist[esweep],biblioteca[tipo] DO BEGIN
    IF tswval^.panel_int<=nval THEN BEGIN
      voriginal:=netlist[esweep].val[tswval^.panel_int];
      WHILE nref>0 DO DesalocarReferencia;
      WHILE AlocarReferencia and (nref<tswn^.panel_int) DO;
      Saida('Sweeping '+tswel^.panel_value+' ('+nmval[tswval^.panel_int]+'):');
      IF ssweep^.sel_setting=1 THEN BEGIN
        vmin:=tswmin^.panel_real;
        vmax:=tswmax^.panel_real;
        vstep:=(tswmax^.panel_real-vsweep)/(nref-1)
      END
      ELSE BEGIN
        vmin:=(tswmin^.panel_real/100)*voriginal;
        vmax:=(tswmax^.panel_real/100)*voriginal;
        vstep:=((tswmax^.panel_real/100)*voriginal-vsweep)/(nref-1)
      END;
      lin:=(sescala^.sel_setting=1) or (vmin=0);
      IF lin THEN vstep:=(vmax-vmin)/(nref-1)
      ELSE vstep:=Ex(vmax/vmin,1/(nref-1));
      vsweep:=vmin;
      FOR psweep:=1 TO nref DO BEGIN
        Saida(nome+': '+biblioteca[tipo].nmval[tswval^.panel_int]+'='+Cpct(vsweep)+'; Ref #'+Sri(psweep));
        val[tswval^.panel_int]:=vsweep;
        InvalidarAnalise(nil);
        IniciarAnalise(nil);
        funcao[psweep]^:=funcao[0]^;
        IF lin THEN vsweep:=vsweep+vstep ELSE vsweep:=vsweep*vstep;
      END;
      val[tswval^.panel_int]:=voriginal;
      analise_feita:=FALSE;
      Saida('Sweep completed. Results in refs. #1-#'+Sri(nref));
      IF nref<>tswn^.panel_int THEN Saida('* Memory was enough for only '+Sri(nref)+' functions');
    END
    ELSE Saida('* The element '+tswel^.panel_value+' has only '+Sri(nval)+' value(s)');
  END
  ELSE Saida('* Element '+tswel^.panel_value+' not found');
END;

PROCEDURE AbrirSweep(obj:Xv_opaque);
BEGIN
  close_window(jsweep);
  tswel^.panel_value:=netlist[eedit].nome;
  open_window(jsweep)
END;

PROCEDURE MonteCarlo(obj:Xv_opaque);
VAR
  pnetlist:^ListaNet;
  i,j,k,nrun:INTEGER;
  mm:WORD;
  tol,r:REAL;
BEGIN
  close_window(jmontecarlo);
  WHILE nref>0 DO DesalocarReferencia;
  mm:=numero*SizeOf(elemento);
  IF MaxAvail<mm THEN BEGIN
    Saida('* Not enough memory');
    Exit;
  END;
  GetMem(pnetlist,mm);
  FOR i:=1 TO numero DO pnetlist^[i]:=Netlist[i];
  WHILE AlocarReferencia and (nref<tmonten^.panel_int) DO;
  Saida('Running Monte Carlo analysis with '+Sri(nref)+' circuits');
  Randomize;
  FOR nrun:=1 TO nref DO BEGIN
    FOR i:=1 TO numero DO WITH Netlist[i] DO BEGIN
      k:=biblioteca[tipo].nval;
      FOR j:=1 TO k DO
        IF not ((tipo=FonteV) or ((tipo=FonteF) and (j=2))) THEN BEGIN
          IF (tipo=Capacitor) or (tipo=Indutor) or (tipo=Transformador) THEN
            tol:=tmontetlcm^.panel_real
          ELSE tol:=tmontetr^.panel_real;
          IF sdistribuicao^.sel_setting=1 THEN r:=2*Random-1 ELSE r:=RandGauss/3;
          val[j]:=pnetlist^[i].val[j]*(1+tol*r);
        END
    END;
    InvalidarAnalise(nil);
    IniciarAnalise(nil);
    funcao[nrun]^:=funcao[0]^;
    Saida('Circuit #'+Sri(nrun)+' completed');
  END;
  analise_feita:=FALSE;
  Saida('Monte Carlo analysis completed.'^M^J'Results in refs. #1-#'+Sri(nref));
  IF nref<>tmonten^.panel_int THEN Saida('* Memory was enough for only '+Sri(nref)+' circuits');
  FOR i:=1 TO numero DO Netlist[i]:=pnetlist^[i];
  FreeMem(pnetlist,mm);
END;

{$F-}

PROCEDURE set_default;
BEGIN
  w_base^.mouse_obj:=o_base
END;

BEGIN
  DoisPi:=2*Pi; RadGraus:=180/Pi; LnDb:=10/Ln(10); rede:='ifft';
  placa:=0; modo:=0;
  IF ParamCount=3 THEN BEGIN
    Val(ParamStr(2),placa,iii);
    Val(ParamStr(3),modo,iii)
  END;
  xv_init(placa,modo);
  IF GetMaxColor=1 THEN FOR i:=-1 TO maxref DO cor[i]:=1
  ELSE IF placa=CGA THEN BEGIN
    cor[-1]:=2;
    cor[0]:=3;
    FOR i:=1 TO maxref DO cor[i]:=i mod 3+1;
  END
  ELSE BEGIN
    cor[-1]:=7;
    cor[0]:=15;
    FOR i:=1 TO maxref DO cor[i]:=i mod 14+1;
  END;
  InitSprites(cor[0],cor[2]);
  New(funcao[0]); atual:=0;
  InvalidarAnalise(nil);
  menu2:=xv_create(menu);
  WITH menu2^ DO BEGIN
    item_create('frequency response');
    item_create('transfer function');
    item_create('poles and zeros');
    item_create('messages');
    xv_label:='Save:';
    notify_handler:=TratarMenu2
  END;
  menu3:=xv_create(menu);
  WITH menu3^ DO BEGIN
    item_create('store last results');
    item_create('delete last reference');
    item_create('delete all references');
    item_create('read reference');
    item_create('restore last reference');
    item_create('save all references');
    xv_label:='References:';
    notify_handler:=TratarMenu3
  END;
  menu1:=xv_create(menu);
  WITH menu1^ DO BEGIN
    item_create('netlist');
    item_create('messages');
    item_create('analysis');
    item_create('frequency response');
    item_create('poles and zeros');
    item_create('edit');
    item_create('references');
    item_create('save');
    item_create('informations');
    item_create('back');
    item_create('roots parameters');
    item_create('Monte Carlo');
    item_create('quit');
    item_submenu[7]:=menu3;
    item_submenu[8]:=menu2;
    xv_label:='options:';
    notify_handler:=TratarMenu1
  END;
  jfrequencia:=xv_create(frame);
  WITH jfrequencia^ DO BEGIN
    dx:=GetMaxX; dy:=GetMaxY;
    xv_label:='IFFT';
    menu_name:=menu1;
    adjust_exit:=FALSE;
  END;
  cresposta:=xv_create(canvas);
  WITH cresposta^ DO BEGIN
    notify_handler:=PlotarRespostaEmFrequencia;
    event_handler:=EventosResposta;
    fore_color:=c_white;
    back_color:=c_black;
    menu_name:=menu1;
  END;
  normal_length:=7;
  jextra:=xv_create(frame);
  WITH jextra^ DO BEGIN
    xv_label:='Roots Calculation Parameters';
    dx:=254; dy:=116;
    menu_name:=menu1;
  END;
  ttol:=xv_create(textfield);
  WITH ttol^ DO BEGIN
    xv_label:='Root tolerance';
    field_type:=real_field;
    panel_real:=1e-11;
    notify_handler:=InvalidarRaizes;
  END;
  ttolm:=xv_create(textfield);
  WITH ttolm^ DO BEGIN
    xv_label:='Derivative tolerance';
    field_type:=real_field;
    panel_real:=1e-11;
    notify_handler:=InvalidarRaizes; y:=15;
  END;
  treal:=xv_create(textfield);
  WITH treal^ DO BEGIN
    xv_label:='Real approximation';
    field_type:=real_field;
    panel_real:=1.1;
    notify_handler:=InvalidarRaizes; y:=30;
  END;
  timag:=xv_create(textfield);
  WITH timag^ DO BEGIN
    xv_label:='Imag approximation';
    field_type:=real_field;
    panel_real:=1.1;
    notify_handler:=InvalidarRaizes; y:=45;
  END;
  tminimo:=xv_create(textfield);
  WITH tminimo^ DO BEGIN
    xv_label:='Minimum non zero value';
    field_type:=real_field;
    panel_real:=1e-8;
    notify_handler:=InvalidarRaizes; y:=60;
  END;
  smetodo:=xv_create(setting);
  WITH smetodo^ DO BEGIN
    xv_label:='Method';
    item_create('Bairstow');
    item_create('Newton-Raphson');
    exclusive:=TRUE;
    sel_setting:=2; y:=75;
    notify_handler:=InvalidarRaizes;
  END;
  jparametros:=xv_create(frame);
  WITH jparametros^ DO BEGIN
    xv_label:='Analysis Parameters';
    dx:=319; dy:=176;
    menu_name:=menu1;
  END;
  tfatorw:=xv_create(textfield);
  WITH tfatorw^ DO BEGIN
    xv_label:='Frequency normalization factor';
    field_type:=real_field; panel_real:=1;
    notify_handler:=InvalidarAnalise;
  END;
  tfatorz:=xv_create(textfield);
  WITH tfatorz^ DO BEGIN
    xv_label:='Impedance normalization factor';
    field_type:=real_field; panel_real:=1; y:=15;
    notify_handler:=InvalidarAnalise;
  END;
  tngrau:=xv_create(textfield);
  WITH tngrau^ DO BEGIN
    xv_label:='Estimated numerator degree  ';
    field_type:=int_field; y:=30; {valor inicializado em AcharOrdem}
    notify_handler:=InvalidarAnalise;
  END;
  tdgrau:=xv_create(textfield);
  WITH tdgrau^ DO BEGIN
    xv_label:='Estimated denominator degree';
    field_type:=int_field; y:=45; {valor inicializado em AcharOrdem}
    notify_handler:=InvalidarAnalise;
  END;
  sforcar:=xv_create(setting);
  WITH sforcar^ DO BEGIN
    y:=60;
    xv_label:='Force degrees';
    Item_create('yes');
    Item_create('no');
    exclusive:=TRUE;
    sel_setting:=2;
    notify_handler:=InvalidarDenominador;
  END;
  tdispden:=xv_create(textfield);
  WITH tdispden^ DO BEGIN
    xv_label:='Denominator dispersion';
    field_type:=real_field; panel_real:=1e6; y:=75;
    notify_handler:=InvalidarDenominador;
  END;
  tdispnum:=xv_create(textfield);
  WITH tdispnum^ DO BEGIN
    xv_label:='Numerator dispersion  ';
    field_type:=real_field; panel_real:=1e6; y:=90;
    notify_handler:=InvalidarNumerador;
  END;
  sraizes:=xv_create(setting);
  WITH sraizes^ DO BEGIN
    y:=105;
    xv_label:='Compute poles and zeros';
    item_create('yes');
    item_create('no');
    exclusive:=TRUE;
    sel_setting:=2;
  END;
  snorm:=xv_create(setting);
  WITH snorm^ DO BEGIN
    xv_label:='Normalized results';
    y:=120;
    item_create('yes');
    item_create('no');
    exclusive:=TRUE;
    sel_setting:=1;
    notify_handler:=ZerarGrafico;
  END;
  tsaida:=xv_create(textfield);
  WITH tsaida^ DO BEGIN
    y:=135;
    xv_label:='Output node';
    field_type:=int_field; panel_int:=1; min_value:=0;
    notify_handler:=InvalidarNumerador;
  END;
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='Analyze';
    y:=135; x:=242;
    notify_handler:=IniciarAnalise;
    set_default;
  END;
  jterminal:=xv_create(frame);
  WITH jterminal^ DO BEGIN
    xv_label:='Messages';
    dx:=319; dy:=250; x:=320;
    menu_name:=menu1;
  END;
  normal_bsize:=30000;
  ttymsg:=xv_create(tty);
  WITH ttymsg^ DO BEGIN
    fore_color:=c_white;
    back_color:=c_black
  END;
  jpfrequencia:=xv_create(frame);
  normal_length:=20;
  WITH jpfrequencia^ DO BEGIN
    xv_label:='Frequency Response Parameters';
    dx:=319; dy:=176;
    menu_name:=menu1;
  END;
  twmin:=xv_create(textfield);
  WITH twmin^ DO BEGIN
    xv_label:='Minimum frequency';
    field_type:=real_field;
  notify_handler:=ZerarGrafico;
  END;
  twmax:=xv_create(textfield);
  WITH twmax^ DO BEGIN
    xv_label:='Maximum frequency';
    field_type:=real_field; y:=15;
    notify_handler:=ZerarGrafico;
  END;
  tgmin:=xv_create(textfield);
  WITH tgmin^ DO BEGIN
    xv_label:='Minimum gain ';
    field_type:=real_field; y:=30;
  END;
  tgmax:=xv_create(textfield);
  WITH tgmax^ DO BEGIN
    xv_label:='Maximum gain ';
    field_type:=real_field; y:=45;
  END;
  tfmin:=xv_create(textfield);
  WITH tfmin^ DO BEGIN
    xv_label:='Minimum phase';
    field_type:=real_field; panel_real:=-180; y:=60;
  END;
  tfmax:=xv_create(textfield);
  WITH tfmax^ DO BEGIN
    xv_label:='Maximum phase';
    field_type:=real_field; panel_real:=180; y:=75;
  END;
  tamin:=xv_create(textfield);
  WITH tamin^ DO BEGIN
    xv_label:='Minimum delay';
    field_type:=real_field; panel_real:=-10; y:=90;
  END;
  tamax:=xv_create(textfield);
  WITH tamax^ DO BEGIN
    xv_label:='Maximum delay';
    field_type:=real_field; panel_real:=30; y:=105;
  END;
  slog:=xv_create(setting);
  WITH slog^ DO BEGIN
    xv_label:='Scale';
    item_create('log');
    item_create('lin');
    sel_setting:=1; y:=120;
    exclusive:=TRUE;
    notify_handler:=ZerarGrafico;
  END;
  srads:=xv_create(setting);
  WITH srads^ DO BEGIN
    xv_label:='Units';
    item_create('Rad/s');
    item_create('Hertz');
    sel_setting:=1; y:=135;
    exclusive:=TRUE;
    notify_handler:=ZerarGrafico;
  END;
  splotar:=xv_create(setting);
  WITH splotar^ DO BEGIN
    xv_label:='Plot';
    item_create('grid');
    item_create('phase');
    item_create('delay');
    sel_setting:=7; y:=120; x:=140;
  END;
  tsegmentos:=xv_create(textfield);
  WITH tsegmentos^ DO BEGIN
    xv_label:='Segments';
    field_type:=int_field; panel_int:=199; min_value:=0; max_value:=xxmax;
    y:=135; value_length:=5; x:=140;
    notify_handler:=ZerarGrafico;
  END;
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='Plot';
    y:=135; x:=266;
    notify_handler:=IniciarResposta;
    set_default;
  END;
  jedit:=xv_create(frame);
  WITH jedit^ DO BEGIN
    dx:=235; x:=6; y:=177; dy:=100;
    xv_label:='Circuit Edition';
    menu_name:=menu1;
  END;
  tenome:=xv_create(message);
  tenome^.xv_label:='Element';
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='-';
    x:=190;
    notify_handler:=MudarElemento;
  END;
  bmais:=xv_create(button);
  WITH bmais^ DO BEGIN
    xv_label:='+';
    x:=210;
    notify_handler:=MudarElemento;
  END;
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='Sweep..';
    x:=122;
    notify_handler:=AbrirSweep;
  END;
  FOR iii:=1 TO 4 DO BEGIN
    tvalor[iii]:=xv_create(textfield);
    WITH tvalor[iii]^ DO BEGIN
      field_type:=real_field;
      y:=iii*15;
      xv_label:='value';
      notify_handler:=AlterarValor;
    END
  END;
  jedit^.mouse_obj:=tvalor[1];
  jraizes:=xv_create(frame);
  WITH jraizes^ DO BEGIN
    dx:=319; dy:=239; y:=240;
    xv_label:='Poles and Zeros';
    menu_name:=menu1;
    set_default;
  END;
  craizes:=xv_create(canvas);
  WITH craizes^ DO BEGIN
    notify_handler:=PlotarPolosEZeros;
    event_handler:=EventosPolosEZeros;
    back_color:=c_black; fore_color:=c_white;
  END;
  jreferencia:=xv_create(frame);
  WITH jreferencia^ DO BEGIN
    dx:=270; dy:=130;
    xv_label:='Function Files';
    menu_name:=menu1;
  END;
  ttitulo:=xv_create(textfield);
  WITH ttitulo^ DO BEGIN
    xv_label:='Circuit';
    notify_handler:=SetarNome;
    set_default;
  END;
  tnsaida:=xv_create(textfield);
  WITH tnsaida^ DO BEGIN
    xv_label:='Output node'; y:=15;
    field_type:=int_field; panel_int:=1;
    value_length:=4;
    notify_handler:=SetarNome;
  END;
  tnumerador:=xv_create(textfield);
  WITH tnumerador^ DO BEGIN
    xv_label:='Numerator  '; y:=30;
  END;
  tdenominador:=xv_create(textfield);
  WITH tdenominador^ DO BEGIN
    xv_label:='Denominator'; y:=45;
  END;
  tzeros:=xv_create(textfield);
  WITH tzeros^ DO BEGIN
    xv_label:='Zeros'; y:=60;
  END;
  tpolos:=xv_create(textfield);
  WITH tpolos^ DO BEGIN
    xv_label:='Poles'; y:=75;
  END;
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='Read';
    notify_handler:=LerReferencia; y:=90;
  END;
  jdiretorio:=xv_create(frame);
  WITH jdiretorio^ DO BEGIN
    xv_label:='Directory';
    dx:=255; x:=6; y:=23;
    dy:=159;
    menu_name:=menu1;
  END;
  tnetlist:=xv_create(textfield);
  WITH tnetlist^ DO BEGIN
    xv_label:='Netlist';
    value_length:=22;
    IF ParamCount>0 THEN BEGIN
      panel_value:=ParamStr(1);
    END;
    notify_handler:=AbrirNetList;
    set_default;
  END;
  tmask:=xv_create(textfield);
  WITH tmask^ DO BEGIN
    xv_label:='Mask';
    value_length:=25;
    panel_value:='*.net';
    notify_handler:=LerDiretorio; y:=15;
  END;
  cdiretorio:=xv_create(canvas);
  WITH cdiretorio^ DO BEGIN
    y:=30;
    notify_handler:=LerDiretorio;
    event_handler:=EscolherArquivo;
  END;
  jsweep:=xv_create(frame);
  WITH jsweep^ DO BEGIN
    xv_label:='Value Sweep';
    x:=6; y:=278;
    dx:=242;
    dy:=100;
    menu_name:=menu1
  END;
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='Start';
    x:=180;
    y:=60;
    notify_handler:=ExecutarVarredura;
  END;
  tswval:=xv_create(textfield);
  WITH tswval^ DO BEGIN
    xv_label:='Value #';
    x:=120;
    value_length:=5;
    field_type:=int_field;
    panel_int:=1;
    min_value:=1;
    max_value:=4;
  END;
  tswel:=xv_create(textfield);
  WITH tswel^ DO BEGIN
    xv_label:='Element';
    value_length:=6;
  END;
  ssweep:=xv_create(setting);
  WITH ssweep^ DO BEGIN
    xv_label:='Min/max are';
    y:=60;
    item_create('values');
    item_create('%');
    exclusive:=TRUE;
    sel_setting:=2;
  END;
  tswmin:=xv_create(textfield);
  WITH tswmin^ DO BEGIN
    xv_label:='Minimum';
    y:=15;
    field_type:=real_field;
    panel_real:=80;
  END;
  tswmax:=xv_create(textfield);
  WITH tswmax^ DO BEGIN
    xv_label:='Maximum';
    y:=30;
    field_type:=real_field;
    panel_real:=120;
  END;
  tswn:=xv_create(textfield);
  WITH tswn^ DO BEGIN
    xv_label:='Steps';
    y:=45;
    value_length:=4;
    field_type:=int_field;
    panel_int:=5;
    min_value:=2;
    max_value:=maxref;
  END;
  sescala:=xv_create(setting);
  WITH sescala^ DO BEGIN
    xv_label:='Scale';
    item_create('lin');
    item_create('log');
    exclusive:=TRUE;
    sel_setting:=1;
    y:=45; x:=85;
  END;
  jmontecarlo:=xv_create(frame);
  WITH jmontecarlo^ DO BEGIN
   dx:=245; x:=6; y:=177;
   xv_label:='Monte Carlo analysis';
   menu_name:=menu1;
  END;
  normal_length:=6;
  tmonten:=xv_create(textfield);
  WITH tmonten^ DO BEGIN
    xv_label:='Number of circuits';
    field_type:=int_field;
    min_value:=0;
    max_value:=maxref;
    panel_int:=20;
  END;
  tmontetr:=xv_create(textfield);
  WITH tmontetr^ DO BEGIN
    xv_label:='Variability    ';
    field_type:=real_field;
    panel_real:=0.05;
    y:=15;
  END;
  tmontetlcm:=xv_create(textfield);
  WITH tmontetlcm^ DO BEGIN
    xv_label:='Variability: LC';
    field_type:=real_field;
    panel_real:=0.05;
    y:=30;
  END;
  sdistribuicao:=xv_create(setting);
  WITH sdistribuicao^ DO BEGIN
    xv_label:='Distribution';
    item_create('uniform');
    item_create('gaussian');
    exclusive:=TRUE;
    sel_setting:=1;
    y:=45;
  END;
  botao:=xv_create(button);
  WITH botao^ DO BEGIN
    xv_label:='Start';
    y:=60;
    notify_handler:=MonteCarlo;
  END;
  ZoomOut;
  open_window(jfrequencia);
  xv_main_loop(jdiretorio);
  TextMode(80);
END.
