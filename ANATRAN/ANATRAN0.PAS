{Analise Transiente por inversao da Transformada de Laplace}
{V. 1.0 de 25/11/92}
{V. 1.0a de 28/11/92 Mensagens de erro se grau excessivo}
{V. 1.0b de 30/11/92 Polos multiplos recusados}
{V. 1.0c de 19/12/92 Invalidacao quando no. de pontos e mudado}
{V. 1.0d de 16/09/93 Traduzido p/ Ingles, renomeado e arrumado}
{V. 1.1  de 07/11/93 Aceita polos de qualquer multiplicidade}
{V. 1.1a de 16/11/93 Corrigido ganho}
{V. 1.1b de 26/12/94 Corrigida expressao listada c/termo oscilante}
{V. 1.1c de 16/12/97 Atualizado sistema de teclas extendidas}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Graph,XView,GJ;

{$I extkeys.inc}

CONST
  ptmax=400;      {Maximo numero de pontos no grafico}
  tmin0=0;        {Limites iniciais}
  tmax0=50;
  ymin0=-2;
  ymax0=2;
  grafico_valido:BOOLEAN=FALSE;  {Se existe grafico valido}
  funcoes_lidas:BOOLEAN=FALSE;   {Se existem funcoes lidas}
  mg=30;                         {Maximo grau de polinomio}
  mf=5;                          {Maximo numero de funcoes}
  zero=1e-6;
  raio=1.1;
  info=18;
  informacao:ARRAY[1..info] OF STRING[45]=(
  {---------------------------------------------}
  ^M^J'Transient analysis by inversion of the',
  'Laplace transform',
  'By Antonio Carlos Moreirao de Queiroz',
  'COPPE/UFRJ; e-mail acmq@coe.ufrj.br',
  'Version 1.1c - 16/12/1997',
  'The program reads the poles and the',
  'numerator of an s-domain transfer function',
  'and computes the time response for some',
  'inputs: impulse, step, sin(wt), and cos(wt).',
  'It can be used with the IFFT program',
  'for computation of transient responses,',
  'and with filter synthesis programs.',
  'Poles are read from files <name>.r, and',
  'numerators from files <name>.n<function #>.',
  'If <function #>=0, the sufix .n is assumed.',
  'The functions must be normalized.',
  'There are no restrictions on poles multi-',
  'plicities and degree differences.');

TYPE
  tipopolo=(simples,complexo,conjugado,infinito);
  parametros=
    RECORD
      rede:STRING[40];
      nsaida:INTEGER;
      nz,np,npt,xg,yg,ultimo:INTEGER;
      k1,k2,p1,p2:ARRAY[1..mg+2] of REAL;
      num:ARRAY[0..mg+1] OF REAL;
      cte:REAL;
      gy:ARRAY[1..ptmax] of REAL;
      tipo:ARRAY[1..mg+2] of tipopolo;
      ordem:ARRAY[1..mg+2] of INTEGER;
      par:ARRAY[1..mg+2] of INTEGER;
    END;
  cores=ARRAY[0..mf] OF BYTE;

CONST
  cor:cores=(lightgray,yellow,white,lightgreen,lightred,lightblue);
  corCGA:cores=(2,3,1,2,3,1);
  cormono:cores=(1,1,1,1,1,1);

VAR
  n,i,j,k,placa,modo:INTEGER;
  ok:BOOLEAN;
  fdet: ARRAY[1..mf] of parametros;
  arquivo:TEXT;
  sufixo:STRING[4];
  w,t,t1,t2,n1,n2,d1,d2,ang,z1,z2:REAL;
  xmin,xmax,ymin,ymax:INTEGER;    {Limites do grafico em pixels no cgrafico}
  cursorx,cursory:INTEGER;        {Cursor, em pixels no cgrafico}
  atual:INTEGER;                  {Curva atual}
  ax,bx,ay,by,delta:REAL;         {Mapeamento}
  gx:ARRAY[1..ptmax] OF REAL; {Valores X e Y no grafico}
  txt:STRING;

VAR
  MenuPrincipal:Xv_opaque;
  fEscrever,tEscrever:Xv_opaque;
  fLer,trede,tnsaida,bler,sentrada,tw,biniciar:Xv_opaque;
  fprincipal,cgrafico:Xv_opaque;
  fmensagens,tmsg:Xv_opaque;
  fescalas,bplotar,tymax,tymin,txmax,
  fparametros,traio,tzero:Xv_opaque;
  txmin,tpontos:Xv_opaque;

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

PROCEDURE Msg(txt:STRING);
BEGIN
  ttysw_output(tmsg,txt+^M^J)
END;

{$F+}

{Callbacks}

PROCEDURE EscreverArquivo(obj:Xv_opaque);
BEGIN
  IF not grafico_valido THEN BEGIN
    ttysw_output(tmsg,'* Nothing to write'^M^J);
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
  ttysw_output(tmsg,'Written file '+tEscrever^.panel_value+^M^J);
  close_window(obj^.owner)
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
    sufixo:='.r';
    Msg(^M^J'Reading function # '+Sri(n)+': '+rede+'; function (node) # '+Sri(nsaida));
    Assign(arquivo,rede+sufixo);
    {$I-} Reset(arquivo); {$I+}
    ok:=IOResult=0;
    IF not ok THEN BEGIN
      Msg('* Missing file '+rede+sufixo);
      Dec(n); Exit
    END;
    ReadLn(arquivo,np);
    Msg(Sri(np)+' poles:');
    IF np>mg THEN BEGIN
      Msg('* Excessive number of poles');
      Close(arquivo); Dec(n); Exit
    END;
    FOR i:=1 TO np DO BEGIN
      Read(arquivo,p1[i]);
      IF not SeekEoln(arquivo) THEN ReadLn(arquivo,p2[i]) ELSE p2[i]:=0;
      Msg('p'+Sri(i)+':'+Sre(p1[i],14,8)+' '+Sre(p2[i],14,8)+'j');
    END;
    Close(arquivo);
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
    Msg(Sri(nz)+' zeros; numerator:');
    IF nz>mg THEN BEGIN
      Msg('* Numerator with excessive degree');
      Dec(n); Close(arquivo); Exit
    END;
    FOR i:=0 TO nz DO BEGIN
      ReadLn(arquivo,num[i]);
      Msg('n'+Sri(i)+':'+Sre(num[i],14,8))
    END;
    IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte)
    ELSE cte:=1;
    Msg('Multiplying cte.:'+Sre(cte,14,8)+^J^M);
    Close(arquivo);
    {Colocar a entrada}
    CASE sentrada^.sel_setting OF
      1:Msg('Impulse');
      2:BEGIN
        np:=np+1;
        p1[np]:=0; p2[np]:=0;
        Msg('Step: added pole p'+Sri(np)+' at origin');
      END;
      3,4:BEGIN
        w:=tw^.panel_real;
        IF sentrada^.sel_setting=3 THEN ttysw_output(tmsg,'Sinusoid')
        ELSE ttysw_output(tmsg,'Cosinusoid');
        Msg(' of frequency '+Cpct(w)+' rad/s');
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
    IF nz>=np THEN BEGIN
      FOR i:=np+1 TO nz+1 DO BEGIN tipo[i]:=infinito; ordem[i]:=i-np-1 END;
      Msg('There are poles at infinity up to order '+Sri(nz-np));
      Msg('The response includes impulses and derivarives'^M^J'up to order '+
          Sri(nz-np)+' (not plotted)');
      npt:=nz+1
    END
    ELSE npt:=np;
    {Verificar p¢los}
    ttysw_output(tmsg,^M^J'Testing the poles:'^M^J);
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
            IF par[i]<>0 THEN txt:=txt+'; Conjugate is p'+Sri(par[i])
            ELSE BEGIN
              txt:=txt+'; The conjugate is missing';
              ok:=FALSE
            END
          END;
        conjugado:txt:='is the conjugate of p'+Sri(par[i]);
      END;
      ttysw_output(tmsg,'Pole p'+Sri(i)+': '+txt+'; Order: '+Sri(ordem[i])+^M^J);
    END;
    IF not ok THEN BEGIN
      Msg('* Complex poles must be in conjugate pairs');
      Dec(n);
      Exit
    END;
    {Calcular residuos}
    Msg(^M^J'Poles and their residues:');
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
      IF tipo[k]=infinito THEN Msg('P'+Sri(k)+': Infinity (#'+Sri(ordem[k])+')')
      ELSE Msg('P'+Sri(k)+':'+Sre(p1[k],14,8)+Sre(p2[k],14,8)+'j (#'+Sri(ordem[k])+')');
      Msg('K'+Sri(k)+':'+Sre(k1[k],14,8)+Sre(k2[k],14,8)+'j')
    END;
    {Testando a expansao}
    Randomize;
    z1:=traio^.panel_real*Random; z2:=traio^.panel_real*Random;
    Msg(^M^J'Random test: s='+Sre(z1,12,8)+Sre(z2,12,8)+'j');
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
    Msg('Original expression: '+Sre(t1,12,8)+Sre(t2,12,8)+'j');
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
    Msg('Partial fractions: '+Sre(t1,12,8)+Sre(t2,12,8)+'j');
    DesalocarSistema;
    Msg(^M^J'The time response components are:');
    FOR i:=1 TO npt DO BEGIN
      IF ordem[i]=2 THEN txt:='*t'
        ELSE IF ordem[i]>2 THEN txt:='*t^'+Sri(ordem[i]-1) ELSE txt:='';
      IF Abs(p1[i])>tzero^.panel_real THEN txt:=txt+'*e^('+Sre(p1[i],5,3)+'*t)';
      CASE tipo[i] OF
        simples:Msg('#'+Sri(i)+': '+Sre(k1[i],5,3)+txt);
        complexo:Msg('#'+Sri(i)+': ('+Sre(2*k1[i],5,3)+'*cos('+Sre(p2[i],5,3)+'*t)+'
                     +^M^J+'     '+Sre(-2*k2[i],5,3)+'*sin('+Sre(p2[i],5,3)+'*t))'
                     +txt);
        infinito:BEGIN
                   txt:='i';
                   FOR j:=1 TO ordem[i] DO txt:=txt+'''';
                   Msg('#'+Sri(i)+': '+Sre(k1[i],5,3)+txt+'(t)');
                 END
      END
    END;
    funcoes_lidas:=TRUE;
    grafico_valido:=FALSE;
    atual:=n;
    open_window(fescalas)
  END
END;

PROCEDURE DesenharGrafico(obj:Xv_opaque);
VAR
  i,ii:INTEGER;
  x,y:REAL;
BEGIN
  IF not funcoes_lidas THEN Exit;
  close_window(fescalas);
  WHILE active_w<>fprincipal DO close_window(active_w);
  IF obj<>cgrafico THEN BEGIN
    SetFillStyle(SolidFill,cgrafico^.back_color);
    Bar(0,0,cgrafico^.dx,cgrafico^.dy);
  END;
  IF not grafico_valido THEN FOR i:=1 TO n DO fdet[i].ultimo:=0;
  {Mapeamento}
  xmin:=60;
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
  Line(60,10,60,cgrafico^.dy-12);
  Line(60,cgrafico^.dy-12,cgrafico^.dx-10,cgrafico^.dy-12);
  SetTextJustify(RightText,TopText);
  OutTextXY(60,10,Sre(tymax^.panel_real,5,2));
  SetTextJustify(RightText,BottomText);
  OutTextXY(60,cgrafico^.dy-10,Sre(tymin^.panel_real,5,2));
  SetTextJustify(RightText,TopText);
  OutTextXY(cgrafico^.dx-10,cgrafico^.dy-10,Sre(txmax^.panel_real,5,2));
  SetTextJustify(LeftText,TopText);
  OutTextXY(60,cgrafico^.dy-10,Sre(txmin^.panel_real,5,2));
  {Calculo e plotagem}
  cursorx:=-10; cursory:=-10;
  grafico_valido:=TRUE;
  delta:=(txmax^.panel_real-txmin^.panel_real)/(tpontos^.panel_int-1);
  x:=txmin^.panel_real;
  FOR i:=1 TO tpontos^.panel_int DO BEGIN
    gx[i]:=x;
    FOR ii:=1 TO n DO WITH fdet[ii] DO BEGIN
      {Calcula, se necessario}
      IF i>ultimo THEN BEGIN
        n1:=0;
        FOR k:=1 TO np DO BEGIN
          d1:=p1[k]*x;
          t:=1;
          FOR j:=1 TO ordem[k]-1 DO t:=t*x/j;
          IF d1>-88 THEN d1:=Exp(d1) ELSE d1:=0;
          IF tipo[k]=simples THEN n1:=n1+t*d1*k1[k]
          ELSE IF tipo[k]=complexo THEN BEGIN
            d2:=p2[k]*x;
            n1:=n1+2*t*d1*(k1[k]*Cos(d2)-k2[k]*Sin(d2));
          END
        END;
        gy[i]:=n1;
      END;
      {Plota}
      IF i>1 THEN MoveTo(xg,yg);
      xg:=Round(ax*gx[i]+bx);
      yg:=Round(ay*gy[i]+by);
      SetColor(cor[ii]);
      IF i>1 THEN LineTo(xg,yg) ELSE MoveTo(xg,yg);
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
  IF (ie_shiftcode=1) or (ie_code=MS_MIDDLE) THEN BEGIN
    {Acha o ponto mais proximo}
    {Precisa do 1.0 multiplicando}
    i:=Round(1.0*(tpontos^.panel_int-1)*(ie_locx-xmin)/(xmax-xmin))+1;
    IF (i>=1) and (i<=fdet[n].ultimo) THEN BEGIN
      IF ie_code=MS_MIDDLE THEN BEGIN
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
      Bar3d(cgrafico^.dx-84,7,cgrafico^.dx-10,33,0,FALSE);
      k:=cgrafico^.dx-82;
      OutTextXY(k,9,'curve '+Sri(atual));
      OutTextXY(k,17,'t:'+Sre(gx[i],6,3));
      OutTextXY(k,25,'y:'+Sre(fdet[atual].gy[i],6,3));
    END
  END
  ELSE CASE ie_code of
    Ord('+'):BEGIN
          tymax^.panel_real:=tymin^.panel_real+(tymax^.panel_real-tymin^.panel_real)/2;
          DesenharGrafico(nil)
        END;
    Ord('-'):BEGIN
          tymax^.panel_real:=tymin^.panel_real+(tymax^.panel_real-tymin^.panel_real)*2;
          DesenharGrafico(nil)
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
    END
END;

PROCEDURE TratarMenuPrincipal(obj:Xv_opaque);
BEGIN
  CASE obj^.sel_menu OF
    1:{Ler Dados}
      open_window(fLer);
    2:{Escrever Dados}
      open_window(fEscrever);
    3:{Processar Dados}
      open_window(fescalas);
    4:{Parametros}
      open_window(fparametros);
    5:{Mensagens}
      open_window(fMensagens);
    6:{Informacoes}
      FOR i:=1 TO info DO ttysw_output(tmsg,informacao[i]+^M^J);
    7:{Terminar}
      xv_end:=TRUE;
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
END;

{$F-}

PROCEDURE Default;
BEGIN
  o_base^.owner^.mouse_obj:=o_base
END;

BEGIN
  normal_bsize:=10000;
  c_active:=3;
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
  {Menu creation}
  {Menu for fEscrever}
  {Menu for fescalas}
  {Menu for fLer}
  {Menu for fprincipal}
  {Menu for cgrafico}
  {Menu for fmensagens}
  MenuPrincipal:=xv_create(menu);
  WITH MenuPrincipal^ DO BEGIN
    xv_label:='Menu:';
    item_create('include function');
    item_create('write table');
    item_create('set scales');
    item_create('parameters');
    item_create('messages');
    item_create('informations');
    item_create('quit');
    sel_menu:=1;
    notify_handler:=TratarMenuPrincipal;
  END;
  {Interface objects creation}
  fEscrever:=xv_create(frame);
  WITH fEscrever^ DO BEGIN
    xv_label:='Write table';
    y:=100;
    dx:=319;
    dy:=40;
    dymin:=40;
    menu_name:=MenuPrincipal;
  END;
  tEscrever:=xv_create(textfield);
  WITH tEscrever^ DO BEGIN
    xv_label:='File';
    value_length:=33;
    panel_value:='out.tra';
    notify_handler:=EscreverArquivo;
  END;
  fescalas:=xv_create(frame);
  WITH fescalas^ DO BEGIN
    xv_label:='Scales';
    y:=100;
    dx:=250;
    dy:=114;
    menu_name:=MenuPrincipal;
  END;
  tpontos:=xv_create(textfield);
  WITH tpontos^ DO BEGIN
    xv_label:='Points';
    y:=60;
    field_type:=int_field;
    panel_int:=200;
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
    xv_label:='Include function';
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
    xv_label:='Read the function';
    x:=67;
    y:=60;
    notify_handler:=LerArquivo;
  END;
  fprincipal:=xv_create(frame);
  WITH fprincipal^ DO BEGIN
    xv_label:='Anatran';
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
    dy:=239;
    menu_name:=MenuPrincipal;
  END;
  tmsg:=xv_create(tty);
  fparametros:=xv_create(frame);
  WITH fparametros^ DO BEGIN
    xv_label:='Parameters';
    y:=100;
    dx:=319;
    dy:=56;
    dymin:=56;
    menu_name:=MenuPrincipal;
  END;
  tzero:=xv_create(textfield);
  WITH tzero^ DO BEGIN
    xv_label:='Minimum non-zero number';
    y:=15;
    value_length:=14;
    field_type:=real_field;
    panel_real:=zero;
  END;
  traio:=xv_create(textfield);
  WITH traio^ DO BEGIN
    xv_label:='Interpolation radius';
    value_length:=17;
    field_type:=real_field;
    panel_real:=raio;
  END;
  open_window(fprincipal);
  xv_main_loop(fLer);
  RestoreCrtMode
END.
