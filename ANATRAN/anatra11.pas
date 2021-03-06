{Inversor de Transformadas de Laplace}
{V. 1.0 de 31/7/2001 - Extraido do Teslasim}
{V. 1.1 de 22/9/2002 - Corrigida desnormaliza??o na resposta ao impulso}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Graph,XView,GJ;

{$I extkeys.inc}

CONST
  ptmax=600;      {Maximo numero de pontos no grafico}
  tmin0=0;        {Limites iniciais}
  tmax0=100;
  ymin0=-2;
  ymax0=2;
  grafico_valido:BOOLEAN=FALSE;  {Se existe grafico valido}
  funcoes_lidas:BOOLEAN=FALSE;   {Se existem funcoes lidas}
  escalas_normalizadas:BOOLEAN=FALSE;
  mg=12;                         {Maximo grau de polinomio}
  mf=6;                          {Maximo numero de funcoes}
  zero=1e-6;
  raio=1.1;
  info=14;
  informacao:ARRAY[1..info] OF STRING[45]=(
  {---------------------------------------------}
  '+-------------------------------------------+',
  'Laplace Transform inverter',
  'By Antonio Carlos Moreirao de Queiroz',
  'COPPE/UFRJ; e-mail acmq@coe.ufrj.br',
  'Version 1.1 - 22/09/2002',
  '(Adapted from the Teslasim program)',
  'The program can read polynomials describing',
  'the Laplace transform of the impulse response',
  'of an arbitrary system and compute the time',
  'response to some input signals.',
  'The required transforms can be generated by',
  'the IFFT program, by saving the transfer',
  'functions or the poles and zeros.',
  '+-------------------------------------------+'
  );
TYPE
  polinomio=ARRAY [0..mg+1] of REAL;
  raizes=ARRAY [1..mg+2] of REAL;
  tipopolo=(simples,complexo,conjugado,infinito);
  parametros=
    RECORD
      rede:STRING[40];
      nsaida:INTEGER;
      nz,np,npt,xg,yg,ultimo:INTEGER;
      k1,k2,p1,p2:raizes;
      num,den:polinomio;
      cte:REAL;
      gy:ARRAY[1..ptmax] of REAL;
      tipo:ARRAY[1..mg+2] of tipopolo;
      ordem:ARRAY[1..mg+2] of INTEGER;
      par:ARRAY[1..mg+2] of INTEGER;
      fator: REAL;
    END;
  cores=ARRAY[0..mf] OF BYTE;

CONST
  cor:cores=(lightgray,yellow,white,lightgreen,lightred,lightblue,red);
  corCGA:cores=(2,3,1,2,3,1,2);
  cormono:cores=(1,1,1,1,1,1,1);

VAR
  n,i,j,k,placa,modo:INTEGER;
  ok:BOOLEAN;
  fdet: ARRAY[1..mf] of parametros;
  arquivo:TEXT;
  sufixo:STRING[4];
  w,t,t1,t2,n1,n2,d1,d2,ang,z1,z2,maximo:REAL;
  xmin,xmax,ymin,ymax:INTEGER;    {Limites do grafico em pixels no cgrafico}
  cursorx,cursory:INTEGER;        {Cursor, em pixels no cgrafico}
  atual:INTEGER;                  {Curva atual}
  ax,bx,ay,by,delta:REAL;         {Mapeamento}
  gx:ARRAY[1..ptmax] OF REAL; {Valores X e Y no grafico}
  txt:STRING;

VAR
  MenuPrincipal,MenuTty,Menufio:Xv_opaque;
  fEscrever,tEscrever,bEscrever:Xv_opaque;
  fLer,trede,tnsaida,bler,sentrada,tw,biniciar:Xv_opaque;
  fprincipal,cgrafico:Xv_opaque;
  fmensagens,tmsg:Xv_opaque;
  fescalas,bplotar,tymax,tymin,txmax,
  fparametros,traio,tzero,ttol,ttolm,treal,timag,stestar:Xv_opaque;
  txmin,tpontos:Xv_opaque;

PROCEDURE Msg(txt:STRING);
BEGIN
  ttysw_output(tmsg,txt+^M^J)
END;

FUNCTION Sre(x:REAL; cm,dc:INTEGER):STRING;
VAR
  txt:STRING;
BEGIN
  Str(x:cm:dc,txt);
  Sre:=txt
END;

FUNCTION Sri(x:INTEGER):STRING;
VAR
  txt:STRING;
BEGIN
  Str(x,txt);
  Sri:=txt
END;

PROCEDURE Msgt(txt:STRING);
BEGIN
  IF stestar^.sel_setting=1 THEN ttysw_output(tmsg,txt+^M^J)
END;

FUNCTION LimY(y:REAL):INTEGER;
BEGIN
  IF y>5000 THEN LimY:=5000
  ELSE IF y<-5000 THEN LimY:=-5000
    ELSE LimY:=Round(y)
END;

PROCEDURE Informacoes;
BEGIN
  FOR i:=1 TO info DO ttysw_output(tmsg,informacao[i]+^M^J);
END;

PROCEDURE Biv(n0:INTEGER; a1:polinomio; VAR Re,Im:raizes);
CONST
  imax=50;
VAR
  a2,c1,c2:polinomio;
  tolm,t,tol,p1,p2,d,xr,xi,p,d1,d2,e1,e2:REAL;
  feito:BOOLEAN;
  i,j,nn,n,ordem:INTEGER;

BEGIN
  IF n0=0 THEN BEGIN Msg('No finite roots'); Exit END;
  tol:=ttol^.panel_real; tolm:=ttolm^.panel_real;
  xr:=treal^.panel_real; xi:=timag^.panel_real;
  feito:=FALSE; ordem:=0; nn:=0; n:=n0;
  FOR i:=0 TO n DO a2[i]:=0;
  {Elimina??o de ra?zes na origem}
  WHILE (n>1) and (a1[0]=0) DO BEGIN
    Re[n]:=0; Im[n]:=0;
    n:=n-1;
    FOR i:=0 TO n DO a1[i]:=a1[i+1]
  END;
  WHILE NOT feito DO BEGIN
    IF n>1 THEN BEGIN
      {Calculo dos valores do polin?mio (p) e de sua derivada (d)}
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
      {C?lculo do erro. Esta forma dificulta overflow}
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
      {Testa poss?vel ra?z m?ltipla}
      d:=Abs(d1)+Abs(d2);
      p:=Abs(p1)+Abs(p2);
      IF (d<tolm) and (p<tolm) THEN BEGIN
        {deriva o polin?mio e continua}
        IF ordem=0 THEN BEGIN c1:=a1; c2:=a2 END;
        FOR i:=1 TO n DO BEGIN
          a1[i-1]:=a1[i]*i/n;
          a2[i-1]:=a2[i]*i/n;
        END;
        n:=n-1; ordem:=ordem+1;
      END
      ELSE BEGIN
        {Atualiza ra?zes}
        xr:=xr-e1;
        xi:=xi-e2;
        {Testa converg?ncia}
        t:=Abs(e1)+Abs(e2);
        IF t<tol THEN BEGIN
          {Armazena ra?zes calculadas}
          FOR i:=n+ordem DOWNTO n DO BEGIN
            Re[i]:=xr; Im[i]:=xi;
          END;
          {Rep?e polin?mio original, se for o caso}
          IF ordem>0 THEN BEGIN
            a1:=c1; a2:=c2; n:=n+ordem;
          END;
          {Deflaciona polin?mio}
          FOR i:=0 TO ordem DO BEGIN
            FOR j:=n-1 DOWNTO 1 DO BEGIN
              a1[j]:=Cmult(xr,xi,a1[j+1],a2[j+1])+a1[j];
              a2[j]:=Imag+a2[j];
            END;
            n:=n-1;
            FOR j:=0 TO n DO
              BEGIN a1[j]:=a1[j+1]; a2[j]:=a2[j+1] END
          END;
          {Prepara c?lculo da pr?xima ra?z}
          IF (Abs(xi)>0.01) THEN xi:=-xi ELSE xi:=0.1;
          IF ordem>0 THEN xr:=xr-0.01; {evita derivada 0 a seguir}
          ordem:=0; nn:=0
        END
        ELSE BEGIN
          nn:=nn+1;
          {Demorando a convergir}
          IF nn>imax THEN BEGIN
            IF KeyPressed THEN BEGIN
              Msg('* Interrupted');
              Exit
            END;
            tol:=tol*10;
            Msg('*  Tolerance increased to '+Sre(tol,10,-1));
            nn:=0;
          END
        END
      END
    END
    ELSE BEGIN
      {Ultimas ra?zes}
      d:=-(Sqr(a1[1])+Sqr(a2[1]));
      xr:=(a1[0]*a1[1]+a2[0]*a2[1])/d;
      xi:=(a2[0]*a1[1]-a1[0]*a2[1])/d;
      feito:=TRUE; nn:=0;
      FOR i:=n+ordem DOWNTO n DO BEGIN
        Re[i]:=xr; Im[i]:=xi;
      END
    END
  END;
END; {Biv}

PROCEDURE CalcularExpansao(n:INTEGER);
BEGIN
  WITH fdet[n] DO BEGIN
    Msg('Normalization factor:'+Sre(fator,7,3)+' rad/s');
    IF nz>=np THEN BEGIN
      FOR i:=np+1 TO nz+1 DO BEGIN tipo[i]:=infinito; ordem[i]:=i-np-1 END;
      Msg('There are poles at infinity up to order '+Sri(nz-np));
      Msg('The response includes impulses and derivarives'^M^J'up to order '+
          Sri(nz-np)+' (not plotted)');
      npt:=nz+1
    END
    ELSE npt:=np;
    {Verificar p?los}
    Msgt('Testing the poles:');
    FOR i:=1 TO np DO BEGIN
      ordem[i]:=1; par[i]:=0;
      IF Abs(p2[i])<tzero^.panel_real THEN tipo[i]:=simples
      ELSE tipo[i]:=complexo;
      FOR k:=1 TO i-1 DO BEGIN
        IF (Abs(p2[i]-p2[k])<tzero^.panel_real) and (Abs(p1[i]-p1[k])<tzero^.panel_real) THEN Inc(ordem[i]);
        IF (tipo[i]=complexo) and (par[i]=0) and
           (tipo[k]=complexo) and (par[k]=0) and
           (Abs(p2[i]+p2[k])<tzero^.panel_real) and (Abs(p1[i]-p1[k])<tzero^.panel_real) THEN BEGIN
             tipo[i]:=conjugado;
             par[i]:=k; par[k]:=i;
           END
      END
    END;
    ok:=TRUE;
    FOR i:=1 TO np DO BEGIN
      CASE tipo[i] OF
        simples:txt:='is real';
        complexo:BEGIN
            txt:='is complex';
            IF par[i]<>0 THEN txt:=txt+'; conjugate is p'+Sri(par[i])
            ELSE BEGIN
              txt:=txt+'; the conjugate is missing';
              ok:=FALSE
            END
          END;
        conjugado:txt:='is the conjugate of p'+Sri(par[i]);
      END;
      Msgt('Pole p'+Sri(i)+': '+txt+'; order: '+Sri(ordem[i]));
    END;
    IF not ok THEN BEGIN
      Msg('* Complex poles must be in conjugate pairs');
      Dec(n);
      Exit
    END;
    {Calcular residuos}
    Msgt('Poles and their residues:');
    {Montar sistema de equacoes}
    IF not AlocarSistema(npt,1) THEN BEGIN
      Msg('* Not enough memory');
      Dec(n);
      Exit
    END;
    dmin:=tzero^.panel_real;
    ang:=2*Pi/npt;
    FOR i:=1 TO npt DO BEGIN {Cada linha}
      z1:=traio^.panel_real*Cos(ang*(i-1)); z2:=traio^.panel_real*Sin(ang*(i-1));
      FOR j:=1 TO npt DO BEGIN {Cada coluna}
        IF tipo[j]=infinito THEN BEGIN
          d1:=1; d2:=0;
          FOR k:=1 TO ordem[j] DO BEGIN
            d1:=Cmult(d1,d2,z1,z2); d2:=Imag
          END;
          Yr^[i]^[j]:=d1; Yi^[i]^[j]:=d2;
        END
        ELSE BEGIN
          t1:=z1-p1[j]; t2:=z2-p2[j];
          d1:=1; d2:=0;
          FOR k:=1 TO ordem[j] DO BEGIN
            d1:=Cmult(d1,d2,t1,t2); d2:=Imag
          END;
          IF Abs(d1)+Abs(d2)<tzero^.panel_real THEN BEGIN
            Msg('* Please use another interpolation radius');
            Dec(n);
            DesalocarSistema;
            open_window(fparametros);
            Exit
          END;
          Yr^[i]^[j]:=Cdiv(1,0,d1,d2); Yi^[i]^[j]:=Imag
        END
      END;
      d1:=1; d2:=0;
      FOR j:=1 TO np DO BEGIN
        d1:=Cmult(d1,d2,z1-p1[j],z2-p2[j]); d2:=Imag
      END;
      n1:=num[nz]; n2:=0;
      FOR j:=nz-1 DOWNTO 0 DO BEGIN
        n1:=Cmult(n1,n2,z1,z2)+num[j]; n2:=Imag
      END;
      Yr^[i]^[npt+1]:=Cdiv(n1*cte,n2*cte,d1,d2); Yi^[i]^[npt+1]:=Imag
    END;
    {Resolver sistema de equacoes}
    IF not ResolverSistema THEN BEGIN
      Msg('* Singular system of equations');
      Msg('  Check parameters and normalization');
      Dec(n);
      DesalocarSistema;
      open_window(fparametros);
      Exit;
    END;
    FOR k:=1 TO npt DO BEGIN
      k1[k]:=Yr^[k]^[npt+1];
      k2[k]:=Yi^[k]^[npt+1];
      IF tipo[k]=infinito THEN Msgt('P'+Sri(k)+': Infinity (#'+Sri(ordem[k])+')')
      ELSE Msgt('P'+Sri(k)+':'+Sre(p1[k],14,8)+Sre(p2[k],14,8)+'j (#'+Sri(ordem[k])+')');
      Msgt('K'+Sri(k)+':'+Sre(k1[k],14,8)+Sre(k2[k],14,8)+'j')
    END;
    {Testando a expansao}
    IF stestar^.sel_setting=1 THEN BEGIN
      Randomize;
      z1:=traio^.panel_real*Random; z2:=traio^.panel_real*Random;
      Msg('Random test: s='+Sre(z1,12,8)+' '+Sre(z2,12,8)+'j');
      Msg('The two values listed below must be equal');
      d1:=1; d2:=0;
      FOR j:=1 TO np DO BEGIN
        d1:=Cmult(d1,d2,z1-p1[j],z2-p2[j]); d2:=Imag
      END;
      n1:=num[nz]; n2:=0;
      FOR j:=nz-1 DOWNTO 0 DO BEGIN
        n1:=Cmult(n1,n2,z1,z2)+num[j]; n2:=Imag
      END;
      t1:=Cdiv(n1*cte,n2*cte,d1,d2); t2:=Imag;
      Msg('Ratio of polynomials:'^M^J+Sre(t1,20,-1)+' '+Sre(t2,20,-1)+'j');
      t1:=0; t2:=0;
      FOR j:=1 TO npt DO BEGIN
        IF tipo[j]=infinito THEN BEGIN
          d1:=k1[j]; d2:=k2[j];
          FOR k:=1 TO ordem[j] DO BEGIN
            d1:=Cmult(d1,d2,z1,z2); d2:=Imag
          END;
          t1:=t1+d1; t2:=t2+d2
        END
        ELSE BEGIN
          d1:=1; d2:=0;
          FOR k:=1 TO ordem[j] DO BEGIN
            d1:=Cmult(d1,d2,z1-p1[j],z2-p2[j]); d2:=Imag
          END;
          t1:=t1+Cdiv(k1[j],k2[j],d1,d2); t2:=t2+Imag
        END
      END;
      Msg('Partial fractions:'^M^J+Sre(t1,20,-1)+' '+Sre(t2,20,-1)+'j');
    END;
    DesalocarSistema;
    Msg('The time response components are:');
    FOR i:=1 TO npt DO BEGIN
      IF ordem[i]=2 THEN txt:='*t'
        ELSE IF ordem[i]>2 THEN txt:='*t^'+Sri(ordem[i]-1) ELSE txt:='';
      IF Abs(p1[i])>tzero^.panel_real THEN txt:=txt+'*e^('+Sre(p1[i],7,5)+'*t)';
      CASE tipo[i] OF
        simples:Msg('#'+Sri(i)+': '+Sre(k1[i],7,5)+txt);
        complexo:Msg('#'+Sri(i)+': ('+Sre(2*k1[i],7,5)+'*cos('+Sre(p2[i],7,5)+'*t)+'
                     +^M^J+'     '+Sre(-2*k2[i],7,5)+'*sin('+Sre(p2[i],7,5)+'*t))'
                     +txt);
        infinito:BEGIN
                   txt:='i';
                   FOR j:=1 TO ordem[i] DO txt:=txt+'''';
                   Msg('#'+Sri(i)+': '+Sre(k1[i],7,5)+txt+'(t)');
                 END
      END
    END;
    Msg('with t multiplied by '+Sre(fator,12,3));
    funcoes_lidas:=TRUE;
    grafico_valido:=FALSE;
    atual:=n;
    IF not escalas_normalizadas THEN BEGIN
      txmax^.panel_real:=100/fator;
      escalas_normalizadas:=TRUE;
    END;
    open_window(fescalas)
  END
END;

{$F+}

{Callbacks}

PROCEDURE EscreverArquivo(obj:Xv_opaque);
BEGIN
  close_window(obj^.owner);
  IF not grafico_valido THEN BEGIN
    Msg('* Nothing to write');
    Exit
  END;
  Assign(arquivo,tEscrever^.panel_value);
  ReWrite(arquivo);
  FOR i:=1 TO fdet[n].ultimo DO BEGIN
    Write(arquivo,gx[i],' ');
    FOR k:=1 TO n DO Write(arquivo,fdet[k].gy[i],' ');
    WriteLn(arquivo)
  END;
  Close(arquivo);
  Msg('File '+tEscrever^.panel_value+' written'^M^J);
END;

PROCEDURE LerArquivo(obj:Xv_opaque);
BEGIN
  {Notify handler para trede}
  IF n=mf THEN BEGIN
    Msg('* Only '+Sri(mf)+' functions allowed');
    Exit
  END;
  Inc(n);
  {Ler funcao}
  WITH fdet[n] DO BEGIN
    nsaida:=tnsaida^.panel_int;
    rede:=trede^.panel_value;
    Msg(^M^J'Reading function # '+Sri(n)+': '+rede+'; function (node) # '+Sri(nsaida));
    sufixo:='.d';
    Assign(arquivo,rede+sufixo);
    {$I-} Reset(arquivo); {$I+}
    ok:=IOResult=0;
    IF not ok THEN BEGIN
    Msg('* Missing denominator file '+rede+sufixo);
      Dec(n);
      Exit;
    END;
    ReadLn(arquivo,np);
    IF np>mg THEN BEGIN
      Msg('* Excessive number of poles (max='+Sri(mg)+')');
      Close(arquivo); Dec(n); Exit
    END;
    FOR i:=0 TO np DO
      ReadLn(arquivo,den[i]);
    IF not SeekEof(arquivo) THEN ReadLn(arquivo,t) ELSE t:=1;
    IF not SeekEof(arquivo) THEN ReadLn(arquivo,fator) ELSE fator:=1;
    Close(arquivo);
    Msg('Denominator read from file '+rede+sufixo);
    IF nsaida=0 THEN sufixo:='' ELSE Str(nsaida,sufixo);
    sufixo:='.n'+sufixo;
    Assign(arquivo,rede+sufixo);
    {$I-} Reset(arquivo); {$I+}
    ok:=IOResult=0;
    IF not ok THEN BEGIN
      Msg('* Missing file '+rede+sufixo);
      Dec(n); Exit
    END;
    ReadLn(arquivo,nz);
    IF nz>mg THEN BEGIN
      Msg('* Numerator with excessive degree (max='+Sri(mg)+')');
      Dec(n); Close(arquivo); Exit
    END;
    FOR i:=0 TO nz DO
      ReadLn(arquivo,num[i]);
    IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte)
    ELSE cte:=1;
    cte:=cte/t;
    Msg('Numerator read from file '+rede+sufixo);
    Close(arquivo);
    Msg('Laplace transform denominator:');
    FOR i:=0 TO np DO
      Msg('a'+Sri(i)+':'+Sre(den[i],14,8));
    Msg('Laplace transform numerator:');
    FOR i:=0 TO nz DO
      Msg('b'+Sri(i)+':'+Sre(num[i],14,8));
    Msg('Multiplying cte.:'+Sre(cte,14,8));
    Biv(np,den,p1,p2);
    Msg('Poles:');
    FOR i:=1 TO np DO
      Msg('p'+Sri(i)+':'+Sre(p1[i],14,8)+' '+Sre(p2[i],14,8)+'j');
    {Colocar a entrada}
    CASE sentrada^.sel_setting OF
      1:BEGIN
          cte:=cte*fator;
          Msg('Impulse: Response multiplied by '+Sre(fator,10,-1));
        END;
      2:BEGIN
        np:=np+1;
        p1[np]:=0; p2[np]:=0;
        Msg('Step: added pole p'+Sri(np)+' at origin');
      END;
      3,4:BEGIN
        w:=tw^.panel_real/fator;
        IF sentrada^.sel_setting=3 THEN ttysw_output(tmsg,'Sinusoid')
        ELSE ttysw_output(tmsg,'Cosinusoid');
        Msg(' of normalized frequency '+Cpct(w)+' rad/s');
        np:=np+2;
        p1[np-1]:=0; p1[np]:=0;
        p2[np-1]:=w; p2[np]:=-w;
        Msg('Added poles p'+Sri(np-1)+' and p'+Sri(np)+' in jw)');
        IF sentrada^.sel_setting=4 THEN BEGIN
          nz:=nz+1;
          FOR i:=nz DOWNTO 1 DO num[i]:=num[i-1];
          num[0]:=0;
          Msg('Numerator multiplied by s');
        END
        ELSE BEGIN
          cte:=cte*w;
          Msg('Cte. multiplied by w');
        END
      END;
    END;
    rede:=rede+'-n'+Sri(nsaida);
  END;
  CalcularExpansao(n);
END;

PROCEDURE DesenharGrafico(obj:Xv_opaque);
VAR
  i,ii:INTEGER;
  x,xn,y:REAL;
BEGIN
  WHILE active_w<>fprincipal DO close_window(active_w);
  IF obj<>cgrafico THEN BEGIN
    SetFillStyle(SolidFill,cgrafico^.back_color);
    Bar(0,0,cgrafico^.dx,cgrafico^.dy);
  END;
  IF not funcoes_lidas THEN Exit;
  IF not grafico_valido THEN FOR i:=1 TO n DO fdet[i].ultimo:=0;
  {Mapeamento}
  xmin:=80;
  xmax:=cgrafico^.dx-10;
  ymin:=10;
  ymax:=cgrafico^.dy-12;
  ay:=(ymax-ymin)/(tymin^.panel_real-tymax^.panel_real);
  by:=ymax-ay*tymin^.panel_real;
  ax:=(xmax-xmin)/(txmax^.panel_real-txmin^.panel_real);
  bx:=xmax-ax*txmax^.panel_real;
  {grade X}
  SetLineStyle(DottedLn,0,NormWidth);
  SetColor(cor[0]);
  d1:=txmax^.panel_real-txmin^.panel_real;
  IF d1>0 THEN BEGIN
    t1:=Exp(Ln(10)*Round(Ln(d1)/Ln(10)-0.499999));
    t2:=Round(txmin^.panel_real/t1+0.5)*t1;
    WHILE t2<txmax^.panel_real DO BEGIN
      i:=Round(ax*t2+bx);
      Line(i,ymin,i,ymax);
      t2:=t2+t1
    END
  END;
  {grade Y}
  d1:=tymax^.panel_real-tymin^.panel_real;
  IF d1>0 THEN BEGIN
    t1:=Exp(Ln(10)*Round(Ln(d1)/Ln(10)-0.499999));
    t2:=Round(tymin^.panel_real/t1+0.5)*t1;
    WHILE t2<tymax^.panel_real DO BEGIN
      i:=Round(ay*t2+by);
      Line(xmin,i,xmax,i);
      t2:=t2+t1
    END
  END;
  SetLineStyle(SolidLn,0,NormWidth);
  {Eixos}
  SetColor(cgrafico^.fore_color);
  Line(xmin,ymin,xmin,cgrafico^.dy-12);
  Line(xmin,cgrafico^.dy-12,cgrafico^.dx-10,cgrafico^.dy-12);
  SetTextJustify(RightText,TopText);
  OutTextXY(xmin,ymin,Sre(tymax^.panel_real,5,-1));
  SetTextJustify(RightText,BottomText);
  OutTextXY(xmin,cgrafico^.dy-10,Sre(tymin^.panel_real,5,-1));
  SetTextJustify(RightText,TopText);
  OutTextXY(cgrafico^.dx-10,cgrafico^.dy-10,Sre(txmax^.panel_real,5,-1));
  SetTextJustify(LeftText,TopText);
  OutTextXY(xmin,cgrafico^.dy-10,Sre(txmin^.panel_real,5,-1));
  {Calculo e plotagem}
  cursorx:=-10; cursory:=-10;
  grafico_valido:=TRUE;
  delta:=(txmax^.panel_real-txmin^.panel_real)/(tpontos^.panel_int-1);
  x:=txmin^.panel_real;
  maximo:=0;
  FOR i:=1 TO tpontos^.panel_int DO BEGIN
    gx[i]:=x;
    FOR ii:=1 TO n DO WITH fdet[ii] DO BEGIN
      {Calcula, se necessario}
      IF i>ultimo THEN BEGIN
        xn:=x*fator;
        n1:=0;
        FOR k:=1 TO np DO BEGIN
          d1:=p1[k]*xn;
          t:=1;
          FOR j:=1 TO ordem[k]-1 DO t:=t*xn/j;
          IF d1>-88 THEN d1:=Exp(d1) ELSE d1:=0;
          IF tipo[k]=simples THEN n1:=n1+t*d1*k1[k]
          ELSE IF tipo[k]=complexo THEN BEGIN
            d2:=p2[k]*xn;
            n1:=n1+2*t*d1*(k1[k]*Cos(d2)-k2[k]*Sin(d2));
          END
        END;
        gy[i]:=n1;
      END;
      {Plota}
      IF i>1 THEN MoveTo(xg,yg);
      xg:=Round(ax*gx[i]+bx);
      yg:=LimY(ay*gy[i]+by);
      SetColor(cor[ii]);
      IF i>1 THEN LineTo(xg,yg) ELSE MoveTo(xg,yg);
      IF Abs(gy[i])>maximo THEN maximo:=Abs(gy[i]);
    END;
    x:=x+delta;
    IF KeyPressed THEN BEGIN
      fdet[n].ultimo:=i;
      Exit;
    END
  END;
  fdet[n].ultimo:=tpontos^.panel_int
END;

PROCEDURE TratarEventos(obj:Xv_opaque);
VAR
  i,k:INTEGER;
BEGIN
  IF not grafico_valido THEN Exit;
  IF (ie_shiftcode=1) or (ie_code=MS_MIDDLE) or (ie_code=9) THEN BEGIN
    {Acha o ponto mais proximo}
    {Precisa do 1.0 multiplicando}
    i:=Round(1.0*(tpontos^.panel_int-1)*(ie_locx-xmin)/(xmax-xmin))+1;
    IF (i>=1) and (i<=fdet[n].ultimo) THEN BEGIN
      IF (ie_code=MS_MIDDLE) or (ie_code=9) THEN BEGIN
        Inc(atual); IF atual>n THEN atual:=1
      END;
      SetWriteMode(XorPut);
      SetColor(c_white);
      Line(cursorx,ymin,cursorx,ymax);
      Rectangle(cursorx-3,cursory-3,cursorx+3,cursory+3);
      cursorx:=Round(ax*gx[i]+bx);
      cursory:=Round(ay*fdet[atual].gy[i]+by);
      Line(cursorx,ymin,cursorx,ymax);
      Rectangle(cursorx-3,cursory-3,cursorx+3,cursory+3);
      SetWriteMode(NormalPut);
      SetFillStyle(SolidFill,cgrafico^.back_color);
      SetColor(cgrafico^.fore_color);
      Bar3d(cgrafico^.dx-129,7,cgrafico^.dx-7,33,0,FALSE);
      k:=cgrafico^.dx-127;
      OutTextXY(k,9,fdet[atual].rede+' (#'+Sri(atual)+')');
      OutTextXY(k,17,'t:'+Sre(gx[i],13,-1));
      OutTextXY(k,25,'v:'+Sre(fdet[atual].gy[i],13,-1));
    END
  END
  ELSE
    CASE ie_code of
      Ord('+'):BEGIN
          tymax^.panel_real:=tymin^.panel_real+(tymax^.panel_real-tymin^.panel_real)/2;
          DesenharGrafico(nil);
        END;
      Ord('-'):BEGIN
          tymax^.panel_real:=tymin^.panel_real+(tymax^.panel_real-tymin^.panel_real)*2;
          DesenharGrafico(nil);
        END;
      kUpArrow:BEGIN
           t:=(tymax^.panel_real-tymin^.panel_real)/4;
           tymax^.panel_real:=tymax^.panel_real+t;
           tymin^.panel_real:=tymin^.panel_real+t;
           DesenharGrafico(nil);
         END;
      kDownArrow:BEGIN
           t:=(tymax^.panel_real-tymin^.panel_real)/4;
           tymax^.panel_real:=tymax^.panel_real-t;
           tymin^.panel_real:=tymin^.panel_real-t;
           DesenharGrafico(nil);
         END;
      kRightArrow:BEGIN
           t:=(txmax^.panel_real-txmin^.panel_real)/2;
           txmax^.panel_real:=txmax^.panel_real+t;
           txmin^.panel_real:=txmin^.panel_real+t;
           grafico_valido:=FALSE;
           DesenharGrafico(nil);
         END;
      kLeftArrow:BEGIN
           t:=(txmax^.panel_real-txmin^.panel_real)/2;
           txmax^.panel_real:=txmax^.panel_real-t;
           txmin^.panel_real:=txmin^.panel_real-t;
           IF txmin^.panel_real<0 THEN BEGIN
             txmax^.panel_real:=2*t;
             txmin^.panel_real:=0;
           END;
           grafico_valido:=FALSE;
           DesenharGrafico(nil);
         END;
      kHome,Ord('a'):BEGIN
           txmax^.panel_real:=txmin^.panel_real+(txmax^.panel_real-txmin^.panel_real)/2;
           grafico_valido:=FALSE;
           DesenharGrafico(nil);
         END;
      kEnd,Ord('r'):BEGIN
           txmax^.panel_real:=txmin^.panel_real+(txmax^.panel_real-txmin^.panel_real)*2;
           grafico_valido:=FALSE;
           DesenharGrafico(nil);
         END;
      kF1:IF maximo<>0 THEN BEGIN
           tymax^.panel_real:=1.1*maximo;
           tymin^.panel_real:=-1.1*maximo;
           DesenharGrafico(nil);
         END;
      kF2:menu_show(menuprincipal);
      kF10:open_window(fparametros);
      END;
END;

PROCEDURE Plotar(obj:Xv_opaque);
BEGIN
  DesenharGrafico(nil);
END;

PROCEDURE InvalidarGrafico(obj:Xv_opaque);
BEGIN
  grafico_valido:=FALSE
END;

PROCEDURE Reiniciar(obj:Xv_opaque);
BEGIN
  n:=0;
  grafico_valido:=FALSE;
  funcoes_lidas:=FALSE;
  Msg('Plots invalidated.');
  DesenharGrafico(nil);
  open_window(obj^.owner);
END;

PROCEDURE TratarMenuPrincipal(obj:Xv_opaque);
BEGIN
  CASE obj^.sel_menu OF
    1:{Ler transformada}
      open_window(fLer);
    2:{Remover ultima curva}
      IF n>1 THEN BEGIN
        Dec(n);
        DesenharGrafico(nil);
      END
      ELSE Reiniciar(fLer);
    3:{Escrever tabela}
      open_window(fEscrever);
    4:{Processar Dados}
      open_window(fescalas);
    5:{Mensagens}
      open_window(fMensagens);
    6:{Informacoes}
      Informacoes;
    7:{Terminar}
      xv_end:=TRUE;
    8:{Cancel}
      IF active_w<>fprincipal THEN close_window(active_w);
  END;
END;

PROCEDURE TratarMenuTty(obj:Xv_opaque);
BEGIN
  CASE obj^.sel_menu OF
  1:BEGIN
      WITH tmsg^ DO yc:=dy;
      ttysw_output(tmsg,'');
    END;
  2:WITH tmsg^ DO BEGIN
      Assign(arquivo,'anatran.msg');
      ReWrite(arquivo);
      i:=bstart;
      WHILE i<>tend DO BEGIN
        Write(arquivo,Pb^[i]);
        IF i<bsize THEN Inc(i) ELSE i:=0
      END;
      Close(arquivo);
      Msg('Messages saved in file anatran.msg')
    END;
  3:IF active_w<>fprincipal THEN close_window(active_w);
  END;
END;

{$F-}

PROCEDURE Default;
BEGIN
  o_base^.owner^.mouse_obj:=o_base
END;

BEGIN
  normal_bsize:=10000;
  c_active:=2;
  n:=0;
  DetectGraph(placa,modo);
  IF placa=CGA THEN modo:=CGAC1;
  IF ParamCount=2 THEN BEGIN
    Val(ParamStr(1),placa,i);
    Val(ParamStr(2),modo,i)
  END;
  xv_init(placa,modo);
  IF GetMaxColor=3 THEN cor:=corCGA
  ELSE IF GetMaxColor=1 THEN cor:=cormono;
  MenuPrincipal:=xv_create(menu);
  WITH MenuPrincipal^ DO BEGIN
    xv_label:='Menu:';
    item_create('read Laplace transform');
    item_create('remove last curve');
    item_create('write table');
    item_create('set scales');
    item_create('messages');
    item_create('informations');
    item_create('quit');
    item_create('close');
    sel_menu:=2;
    notify_handler:=TratarMenuPrincipal;
  END;
  MenuTty:=xv_create(menu);
  WITH MenuTty^ DO BEGIN
    xv_label:='Messages:';
    item_create('clear messages');
    item_create('save messages');
    item_create('close');
    notify_handler:=TratarMenuTty;
  END;
  {Interface objects creation}
  fEscrever:=xv_create(frame);
  WITH fEscrever^ DO BEGIN
    xv_label:='Write table';
    dx:=319;
    dy:=55;
    dymin:=55;
    menu_name:=MenuPrincipal;
  END;
  tEscrever:=xv_create(textfield);
  WITH tEscrever^ DO BEGIN
    xv_label:='File';
    value_length:=33;
    panel_value:='anatran.tab';
    notify_handler:=EscreverArquivo;
    owner^.mouse_obj:=tEscrever;
  END;
  bEscrever:=xv_create(button);
  WITH bEscrever^ DO BEGIN
    xv_label:='Write';
    y:=15;
    notify_handler:=EscreverArquivo;
    owner^.mouse_obj:=bEscrever;
  END;

  fescalas:=xv_create(frame);
  WITH fescalas^ DO BEGIN
    xv_label:='Scales';
    dx:=250;
    dy:=114;
    menu_name:=MenuPrincipal;
  END;
  tpontos:=xv_create(textfield);
  WITH tpontos^ DO BEGIN
    xv_label:='Points';
    y:=60;
    field_type:=int_field;
    panel_int:=ptmax;
    min_value:=1;
    max_value:=ptmax;
    notify_handler:=InvalidarGrafico;
  END;
  normal_length:=20;
  txmin:=xv_create(textfield);
  WITH txmin^ DO BEGIN
    xv_label:='t minimum';
    field_type:=real_field;
    panel_real:=tmin0;
    notify_handler:=InvalidarGrafico;
  END;
  txmax:=xv_create(textfield);
  WITH txmax^ DO BEGIN
    xv_label:='t maximum';
    y:=15;
    panel_real:=tmax0;
    field_type:=real_field;
    notify_handler:=InvalidarGrafico;
  END;
  tymin:=xv_create(textfield);
  WITH tymin^ DO BEGIN
    xv_label:='y minimum';
    y:=30;
    panel_real:=ymin0;
    field_type:=real_field;
  END;
  tymax:=xv_create(textfield);
  WITH tymax^ DO BEGIN
    xv_label:='y maximum';
    y:=45;
    panel_real:=ymax0;
    field_type:=real_field;
  END;
  bplotar:=xv_create(button);
  WITH bplotar^ DO BEGIN
    xv_label:='Plot';
    y:=75;
    notify_handler:=Plotar;
    owner^.mouse_obj:=bplotar;
  END;
  fLer:=xv_create(frame);
  WITH fLer^ DO BEGIN
    xv_label:='Read Laplace transform';
    dx:=319;
    dy:=99;
    menu_name:=MenuPrincipal;
  END;
  trede:=xv_create(textfield);
  WITH trede^ DO BEGIN
    xv_label:='Function name';
    value_length:=24;
    owner^.mouse_obj:=trede
  END;
  tnsaida:=xv_create(textfield);
  WITH tnsaida^ DO BEGIN
    xv_label:='Function (node) #';
    y:=15;
    value_length:=5;
    field_type:=int_field;
    panel_int:=1;
    min_value:=0;
  END;
  sentrada:=xv_create(setting);
  WITH sentrada^ DO BEGIN
    xv_label:='Input';
    y:=30;
    item_create('impulse');
    item_create('step');
    item_create('sine');
    item_create('cosine');
    exclusive:=TRUE;
    sel_setting:=2;
  END;
  tw:=xv_create(textfield);
  WITH tw^ DO BEGIN
    xv_label:='Frequency (rad/s)';
    y:=45;
    field_type:=real_field;
    panel_real:=1;
  END;
  biniciar:=xv_create(button);
  WITH biniciar^ DO BEGIN
    xv_label:='Restart';
    y:=60;
    notify_handler:=Reiniciar;
  END;
  bler:=xv_create(button);
  WITH bler^ DO BEGIN
    xv_label:='Add curve';
    x:=67;
    y:=60;
    notify_handler:=LerArquivo;
  END;
  fprincipal:=xv_create(frame);
  WITH fprincipal^ DO BEGIN
    xv_label:='Anatran - 2';
    dx:=GetMaxX;
    dy:=GetMaxY;
    menu_name:=MenuPrincipal;
    adjust_exit:=FALSE;
  END;
  cgrafico:=xv_create(canvas);
  WITH cgrafico^ DO BEGIN
    back_color:=c_black;
    fore_color:=c_white;
    notify_handler:=DesenharGrafico;
    event_handler:=TratarEventos;
    menu_name:=MenuPrincipal;
  END;
  fmensagens:=xv_create(frame);
  WITH fmensagens^ DO BEGIN
    xv_label:='Messages';
    x:=320;
    dx:=319;
    dy:=GetMaxY;
    menu_name:=MenuPrincipal;
  END;
  tmsg:=xv_create(tty);
  tmsg^.menu_name:=MenuTty;
  fparametros:=xv_create(frame);
  WITH fparametros^ DO BEGIN
    xv_label:='Numerical control parameters';
    dx:=319;
    dy:=130;
    menu_name:=MenuPrincipal;
  END;
  traio:=xv_create(textfield);
  WITH traio^ DO BEGIN
    xv_label:='Interpolation radius';
    value_length:=17;
    field_type:=real_field;
    panel_real:=raio;
  END;
  tzero:=xv_create(textfield);
  WITH tzero^ DO BEGIN
    xv_label:='Minimum non-zero number';
    y:=15;
    value_length:=14;
    field_type:=real_field;
    panel_real:=zero;
  END;
  ttol:=xv_create(textfield);
  WITH ttol^ DO BEGIN
    xv_label:='Root tolerance';
    field_type:=real_field;
    panel_real:=1e-11;
    y:=30;
  END;
  ttolm:=xv_create(textfield);
  WITH ttolm^ DO BEGIN
    xv_label:='Derivative tol.';
    field_type:=real_field;
    panel_real:=1e-11;
    y:=45;
  END;
  treal:=xv_create(textfield);
  WITH treal^ DO BEGIN
    xv_label:='Real approx.';
    field_type:=real_field;
    panel_real:=1.1;
    y:=60;
  END;
  timag:=xv_create(textfield);
  WITH timag^ DO BEGIN
    xv_label:='Imag approx.';
    field_type:=real_field;
    panel_real:=1.1;
    y:=75;
  END;
  stestar:=xv_create(setting);
  WITH stestar^ DO BEGIN
    xv_label:='List tests';
    item_create('yes');
    item_create('no');
    y:=90;
    exclusive:=TRUE;
    sel_setting:=2;
  END;

  open_window(fprincipal);
  Informacoes;
  xv_main_loop(fLer);
  RestoreCrtMode
END.
