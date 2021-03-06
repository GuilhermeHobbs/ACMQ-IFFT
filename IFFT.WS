.ls1
.op�
Program IFFT
------------

B� Antoni� Carlo� M� d� Queiroz
Associat� Professor
Universidad� Federa� d� Ri� d� Janeiro

Documentation for version 1.3b

Th� �IFF� progra� analyse� linea� circuits� �computin� �transfe� �
function� i� Laplac� transform� Fro� th� transfe� fun�tions� �i� �
� �rati�-o�-polynomial� form� th� progra� ca� comput� pole� �an� �
zero� a� plo� frequenc� respons� graphs� 

Th� �progra� �wa� develope� a� � too� fo� fas� �verific�tio� �o� �
continuou� �tim� �filte� designs� I� i� als� �usefu� �fo� �othe� �
purposes� as:

-    Stabilit� analysi� b� direc� pole� an� zero� calcul�tion.
�    Studie� abou� frequenc� compensatio� o� amplifiers.
-    Studie� abou� compensatio� o� operationa� amplifie� G� �an� �
�����inpu� an� outpu� impedanc� effect� i� filters� 
-    Studie� �abou� �th� effect� o� parasiti� �capacitance� �an� �
�����resistance� i� filters.
- �  Mont� �Carl� analysi� an� stud� o� th� effec� o� �componen� �
�����variations.

User Interface:
---------------

Th� �progra� use� � graphica� use� interfac� wit� windows� �tha� �
work� i� th� followin� way:

-    T� �mov� � window� pres� th� lef� mous� butto� anywher� �i� �
�����th� �windo� fram� an� mov� th� mous� wit� th� butto� �pres�
�����sed.
-    T� �resiz� � window� pres� th� righ� mous� butto� clos� �t� �
�����th� �righ� botto� corne� o� th� windo� an� mov� �th� �mous� �
�����wit� th� butto� pressed.
-    T� �clos� � window� pres� th� middl� mous� butto� �anywher� �
�����i� th� windo� fram�.
-    Windo� �movement� ca� b� impossibl� du� t� �memor� �limita�
�����tions� �an� i� thes� case� � bee� sounds� T� �fre� �memory� �
�����clos� �som� �windows� pu� window� directl� ove� �th� �back�
�����ground� o� remov� references.
-    Pres� comman� button� wit� th� lef� mous� button.
-    Acces� �tex� field� pressin� th� lef� mous� butto� �i� �th� �
�����fiel� �area� Th� mous� curso� disappear� unti� �th� �Retur� �
�����ke� i� pressed� endin� th� edition� Th� Es� ke� clear� �th� �
�����field� an� Ctr�-� recover� th� las� tex� entered� Numerica� �
�����field� wor� i� th� sam� way� bu� th� editio� end� onl� whe� �
������ vali� numbe� i� entered.
-    T� �ope� � menu� pres� th� righ� mous� butto� ove� th� �in�
�����terfac� �objec� tha� hav� th� desire� one� Selec� th� �ite� �
�����movin� �th� mous� an� accep� i� b� pressin� th� lef� �mous� �������button� �T� �dismis� th� men� withou� acceptin� �� �choice� �
�����pres� th� middl� mous� button� � ">� a� th� righ� o� � men� �
�����ite� indicate� tha� ther� i� � submenu� accessibl� b� pres�
�����sin� th� righ� mous� butto� again.
-    Onl� th� control� i� totall� expose� window� ar� immediat��
�����l� accessible� A� attemp� t� acces� � contro� i� � partia��
�����l� �covere� �windo� wil� firs� caus� it� �movemen� �t� �th� �
�����front� i� possible.

� �mous� �i� require� fo� optima� performance� bu� �th� �progra� �
include� �� mous� emulato� drive� fro� th� keyboard� Th� �curso� �
key� comman� th� emulate� mous� cursor� Th� key� Return� �Space� �
an� Es� emulat� th� mous� button� left� middle� an� right� �res�
pectively� �Th� curso� ste� i� selecte� b� th� key� �Home� �PgD� �
an� �PgUp� Whe� th� Shif� ke� i� presse� o� CapsLoc� i� �active� �
th� button� wor� i� toggl� mode� s� � butto� continuousl� �pres�
se� �ca� b� simulated� Th� mous� emulato� i� disabled� �an� �th� �
keyboar� work� normall� whe� ScrollLoc� i� active.

Th� mai� interfac� elemen� o� th� progra� i� � menu� �accessibl� �
i� th� frame� o� al� th� windows� Al� th� function� ca� b� sta��
te� �fro� there� Som� ope� dialo� boxes� som� �ac� �immediately� �
an� �som� hav� submenus� Th� progra� alway� give� som� �feedbac� �
afte� an� command� Ther� ar� som� specia� command� no� liste� i� �
th� menu� an� dialo� boxes� liste� below.

� �tw�-button� mous� ca� als� b� used� Window� an� menu� ca� �b� �
dismisse� b� pressin� bot� button� simultaneously.
 
Keyboard commands in the frequency response graph:
--------------------------------------------------

A/R - Reduces/increases the maximum frequency.
</> - Moves down/up the frequency range.
+/- - Reduces/increases the maximum gain.
G - Toggles the drawing of a grid.
F - Toggles the plotting of phase curves.
T - Toggles the plotting of group delay curves.
L - Frequency scale logarithmic/linear.
Vertical arrows - Move the gain curve.
Horizontal arrows - Move the cursor.
Ctrl- horizontal arrows - Move the cursor faster.
Tab - Changes the selected gain curve.
� � Zoom ou�.

Keyboar� command� in the poles and zeros graph:
-----------------------------------------------

Arrows- Move the plot.
+/- - zoom in/out. 

Mous� commands:
---------------

I� th� tw� graphs� th� mous� move� � curso� an� control� � �zoo� ��function.

Input:
------

Th� progra� begin� b� openin� th� frequenc� respons� windo� �an� �
th� �director� window� I� th� director� window� � �netlis� �fil� �
nam� �ca� b� selecte� wit� th� mous� (lef� button� o� type� �di�
rectly� �Th� mas� fiel� ca� b� use� anytim� t� loo� a� dis� �di�
rectories� �Th� netlis� fiel� ca� b� use� anytim� t� chang� �th� �
circui� bein� analyzed.

Th� �progra� accept� a� inpu� � circui� descriptio� fil� i� �th� �
forma� generate� b� th� EdFi� edito� program� I� i� � tex� �fil� �
wit� �th� followin� format� Al� th� elemen� value� i� Ohms� �F��
rads� Henrys� Amperes� an� Volts:

Firs� line� Numbe� o� nodes� excludin� th� referenc� (nod� 0).
Followin� lines� On� elemen� pe� line:

-    Resistor:
     R<name> <node1> <node2> <R>
-    Inductor:
     L<name> <node1> <node2> <L>
-    Capacitor:
     C<name> <node1> <node2> <C>
-    Transforme� wit� inductance� L11� L22� M1� [� M21� (M21=M1� �
�����i� th� default):
     N<name> <node1+> <node1-> <node2+> <node2-> <L11> <L22> <M12> [<M21>] 
-    Gyrator, with gyration resistance Rg:
     Y<name> <node1+> <node1-> <node2+> <node2-> <Rg>
-    Voltage controlled voltage source (voltage amplifier):
     E<name> <nodeV+> <nodeV-> <nodev+> <nodev-> <Av>
-    Current controlled current source (current amplifier):
     F<name> <nodeI+> <nodeI-> <nodei+> <nodei-> <Ai>
-    Voltage controlled current source (transconductor):
     G<name> <nodeI+> <nodeI-> <nodeV+> <nodeV-> <Gm>
-    Current controlled voltage source (transresistor):
     H<name> <nodeV+> <nodeV-> <nodei+> <nodei->
-    Operationa� �amplifier� �wit� gai� GB/� (G� i� �rad/s� �an� �
�����outpu� resistanc� Ro:
     A<name> <node-> <node+> <output node> <GB> <Ro>
-    Ideal operational amplifier: nullator-norator model: 
     O<name> <input node 1> <input node 2> <output node>
-    Bipolar transistor: hybrid h model
     Q<name> <nodeC> <nodeB> <nodeE> <hfe> <hie> <hre> <hoe>
-    MOS transistor:
     M<name> <nodeD> <nodeG> <nodeS> <Gm> <Gds>
-    Current source:
     I<name> <node+> <node-> <I>
-    Voltage source:
     V<name> <node+> <node-> <V>
-    Voltage source with series resistor (V=1 is the default):
     Z<name> <node-> <node+> <Rs> [<V>]
�Othe� element� ca� b� buil� wit� combination� o� thes� elements� �
Not� tha� th� transisto� model� d� no� includ� capacitances� bu� �
the� �ca� �b� �adde� explicitly� Not� �als� �tha� �th� �curren�-�
controlle� source� hav� th� curren� i� � shor�-circui� branc� a� �
inpu��

Analysi� method:
----------------

Th� progra� operate� wit� � versio� o� th� modifie� noda� anal��
si� �method� s� th� current� i� voltag� source� an� i� �contro��
lin� �shor� circuit� ar� computed� Thei� value� ca� b� �accesse� �
a� "noda� voltages� i� node� abov� th� las� nod� o� th� circuit� �
Th� �progra� list� whil� readin� th� netlis� wha� ar� �th� �nod� �
number� �assigne� t� eac� current� Idea� operationa� �amplifier� �
ar� �treate� a� nullato�-norato� pairs i� � mor� efficien� �way� �
an� thei� outpu� current� ar� no� computed� 

Whe� �th� �Analyz� butto� i� th� analysi� parameter� �windo� �i� �
pressed� �th� �circui� i� analyze� i� � �numbe� �o� �frequencie� �
equall� �space� ove� th� uni� circle� Fro� th� obtaine� �values� �
th� numerato� an� denominato� polynomial� i� "s� o� th� transfe� �
function� �i� �Laplac� transfor� ar� recovere� b� �Fas� �Fourie� �
Transform� (FFT)� an� liste� i� th� message� window� Th� compl��
t� analysi� i� mad� onl� whe� change� i� th� analysi� parameter� �
invalidat� anterio� analysi� results.

Th� metho� i� precise� bu� ca� presen� numerica� problem� i� th� �
circui� i� no� adequatel� normalized� I� th� analysi� parameter� �
windo� ther� ar� som� field� tha� ca� b� initialize� wit� value� �
tha� �contro� th� precisio� o� th� analysis� Th� defaul� �value� �
ar� �usuall� convenien� fo� normalize� circuits� Th� meanin� �o� �
th� item� i� thi� windo� are:

-    Frequenc� �normalizatio� factor� Facto� use� �t� �normaliz� �
�����th� circui� i� frequency� Th� idea� valu� i� th� �geometr��
�����ca� �mea� o� th� circui� pole� an� zeros� Afte� th� �anal��
�����sis� �th� progra� list� wha� woul� b� th� idea� value� �fo� �
�����th� �numerato� �an� denominator� i� applicable� �Fo� �usua� �
�����circuits� �th� �use� valu� mus� b� withi� � decad� �o� �th� �
�����idea� �value� fo� reliabl� results� Som� variation� o� �th� �
�����facto� �t� verif� i� th� progra� insist� i� th� sam� �idea� �
�����value� �i� recommende� whe� i� th� analysi� o� �hig� �orde� �
�����circuit� wit� pole� an� zero� sprea� ove� severa� magnitud� �
�����orders.
-    Impedanc� �normalizatio� factor� Facto� use� �t� �normaliz� �
�����th� circui� i� impedance� Th� sam� observation� apply.
-    Estimate� �numerato� an� denominato� degrees� �Th� �progra� �
�����compute� th� maximu� possibl� denominato� degre� fo� volta�
�����g� �transfe� �function� i� th� circui� base� �o� �� �norma� �
�����tree� liste� afte� th� netlis� i� th� message� window� Thi� �
�����valu� �i� �correc� fo� no�-pathologica� circuits� �an� �th� �
�����progra� wil� no� accep� a� vali� an� analysi� resultin� �i� �
������ �differen� value� Th� estimate� numerato� degre� mus� �b� �
�����se� �b� th� use� i� th� optio� o� forcin� degree� i� �used� �������I� �circuit� wher� th� numerato� degre� i� highe� tha� �th� �
�����denominato� degree� th� numerato� degre� mus� b� se� t� th� �
�����correc� value� o� th� analysi� ma� resul� wrong.
-    Forc� degree� option� an� numerato� an� denominato� disper�
�����sio� �factors� Th� analysi� metho� produce� polynomial� �o� �
�����degree� �tha� ca� b� highe� tha� th� correc� ones� �an� �s� �
�����mus� b� cleane� o� numerica� residues� Th� dispersio� �fac�
�����tor� ca� b� use� fo� thi� purpose� The� defin� th� �maximu� �
�����allowabl� rati� amon� polynomia� coefficient� (normalized)� �
�����an� �ar� use� t� eliminat� to� smal� coefficient� fro� �th� �
�����polynomials� �Th� defaul� setting� ar� usuall� �enoug� �fo� �
�����normalize� circuits� I� som� cases� i� i� mor� practica� t� �
�����directl� �forc� th� numerato� an� denominato� �degree� �(t� �
�����th� estimate� values� tha� mus� b� known)� a� i� th� analy�
�����si� �o� �comple� amplifier� wit� man� �natura� �frequencie� �
�����widel� spaced� o� circuit� wit� nonidea� operationa� ampli�
�����fiers.

References:
-----------

Frequenc� �respons� �plots� an� pole� an� zero� �plots� �ca� �b� �
compare� �wit� save� references� Th� reference� ca� b� �obtaine� �
fro� th� presen� analysi� o� fro� save� files� I� i� possibl� t� �
analyz� � circuit� sav� th� result� a� � reference� edi� som� o� �
th� componen� values� reanalize� an� plo� th� ne� result� comp��
re� wit� th� save� ones� Th� reference� ar� enumerate� fro� � t� �
� maximu� o� 250 o� less� dependin� o� th� availabl� memory� Th� �
reference� �ar� �als� use� i� th� valu� swee� �an� �Mont� �Carl� �
analysis.

Edition:
--------

Th� circui� value� ca� b� edite� i� th� edi� window� Th� editio� �
cause� �th� invalidatio� o� th� las� analysis� an� �th� �circui� �
mus� b� reanalized� Th� edite� circui� canno� b� saved�

Sweep:
------

Ther� �i� a� optio� o� sweepin� � valu� ove� � �specifie� �rang� �
(i� �th� edi� window)� Th� r�sult� ar� save� a� references� �an� �
subsequen� plottin� command� produc� familie� o� curve� �showin� �
th� results� Th� swee� rang� ca� b� specifie� b� absolut� limit� �
o� �percentage� o� th� norma� value� Th� swee� ca� b� linea� �o� �
logarithmic� �Th� origina� circui� i� retained� bu� mus� b� �r��
analize� �i� it� curve� ar� t� appea� i� th� plots� Al� th� �re�
ference� ar� cleare� befor� � sweep.

Mont� Carl� analysis:
---------------------

� ��se� �o� �circuit� �wit� �elemen� �value� �withi� ��specifie� �
tolerance� �i� �automaticall� generate� an� �analyzed� �Al� �th� ��result� ar� store� a� references� a� i� th� swee� analysis� �Th� �
variabilitie� �o� �certai� group� o� element� ca� �b� �specifie� �
independently� �an� �unifor� o� Gaussia� �distribution� �ca� �b� �
used� I� th� Gaussia� distribution� th� specifie� �variabilitie� �
correspon� t� thre� standar� deviations� Ther� i� � men� ite� i� �
th� reference� submen� tha� ca� b� use� t� sav� al� th� frequen�
c� �responses� poles� an� zero� resultin� fro� th� �analysi� �t� �
files� �Th� �file� ca� b� use� fo� compariso� wit� �th� �result� �
obtaine� b� sensitivit� analysi� wit� th� SENS� program� b� �th� �
us� o� th� CPSENS� an� CPSP� programs� (Se� th� SENS� packag� a� �
th� ft� sit� coe.ufrj.br� director� pub/acmq.)

Outpu� files:
------------

Al� �th� result� ca� b� saved� i� separat� tex� file� �accordin� �
t� th� typ� o� result� Th� name� ar� give� automatically� I� �i� �
als� possibl� t� sav� al� th� message� i� th� messag� windo� �a� �
� file� Th� polynomial� an� root� ar� save� i� normalize� �form� �
Th� �normalizatio� facto� use� i� als� save� a� th� en� �o� �th� �
files� Th� referenc� pole� an� zero� ar� save� unnormalized.

Observations:
-------------

Th� progra� ca� hav� problem� i� findin� pole� an� zero� i� som� �
hig�-orde� circuits� I� thes� case� i� wil� lowe� th� �toleranc� �
o� th� root� unti� i� ca� solv� fo� them� an� th� fina� �result� �
ma� b� inaccurate� I� i� importan� t� tur� o� th� automati� pol� �
an� �zer� �computatio� (i� th� analysi� window� �onl� �whe� �th� �
frequenc� normalizatio� facto� i� correctl� adjusted� �otherwis� �
a� �irrecoverabl� �overflo� erro� ma� occur� Fo� �compariso� �o� �
results� th� progra� ca� us� tw� differen� method� fo� computin� �
polynomia� �root� (se� i� th� roo� parameter� window)� �Th� �d��
faul� �metho� i� th� mos� reliable� an� slower� one� �Th� �pole� �
an� �zero� �optio� i� th� mai� men� cause� �th� �computatio� �o� �
pole� an� zero� o� th� presen� functio� an� o� al� th� �refere��
ces� �i� �the� �wer� no� alread� computed� �Th� �changin� �o� �� �
paramete� i� th� root� parameter� windo� cause� th� invalidatio� �
o� th� pole� an� zero� o� th� presen� function� bu� no� th� one� �
o� th� references� Thi� i� t� allo� eas� compariso� o� results.

Th� �progra� wil� driv� an� graphi� boar� supporte� b� th� �.BG� �
graphi� �driver� �(Turb� Pasca� 7.0)� u� t� �640x48� �1� �color� �
mode� �Th� highes� resolutio� mod� wil� b� use� b� default� �bu� �
thi� ca� b� overridde� i� th� comman� line:

		>IFFT <file> <driver> <mode>

Thi� �wil� cop� th� nam� <file� t� th� netlis� nam� tex� �field� �
an� initializ� th� graphi� syste� wit� th� drive� an� mod� �nu��
ber� give� (Ex� "� 1� � CG� 320x20� (...)� "� 4� � CG� �640x200� �
"� �1� �� EG� 640x350� "� 5� � MCG� 640x480� etc.� �Th� �comman� �
lin� command� ar� optional� Th� graphic� driver� mus� b� o� �th� �
cu�ren� director� o� i� � pat� pointe� b� th� environmen� varia��bl� TPBG� (Us� th� DO� "set� comman� t� creat� it)�

Th� �IFF� �progra� i� i� continuou� evolutio� �sinc� �it� �firs� �
version� �writte� �i� BASI� fo� a� H�-7� compute� i� �1984� �Th� �
progra� �wa� porte� t� � PC� rewritte� i� Turb� Pascal� �an� �i� �
199� �rewritte� wit� th� ne� graphica� interface� als� i� �Turb� �
Pascal� 

The EdFil editor program:
-------------------------

Th� EdFi� edito� ca� b� use� t� generat� th� inpu� ne�-lis� fil� �
fo� �th� IFF� program� an� als� fo� othe� programs� �eve� �SPIC� �
(wit� som� editing)� I� wa� writte� afte� th� conclusio� tha� i� �
i� �virtuall� impossibl� t� writ� � textua� netlis� fo� �� �no�-�
trivia� �circui� withou� errors� It� us� i� recommende� fo� �an� �
circui� analysis.

Th� circui� i� draw� o� th� scree� usin� th� curso� key� an� th� �
selecte� �keyboar� �key� �liste� a� th� �botto� �o� �th� �edito� �
screen� � hel� scree� i� assesse� b� th� � key� Name� an� �para�
meter� �fo� th� element� ar� give� b� movin� th� curso� �t� �th� �
componen� an� touchin� th� Retur� key� o� b� Ctr�-X� tha� cause� �
th� progra� t� as� param�ter� fo� al� th� visibl� elements� �Th� �
bes� metho� i� usuall� t� firstl� dra� al� th� circui� an� late� �
giv� th� parameters� Ther� ar� d�faul� name� an� param�ter� �fo� �
al� �elements� Th� parameter� ar� � text� an� ar� repr�duce� �i� �
th� ne�-lis� a� given� unles� fo� formulae� tha� mus� b� �enclo�
se� i� parenth�sis.

Onc� �draw� th� circuit� th� ne�-lis� i� generate� wit� �Ctr�-Q� �
Th� �progra� the� ask� th� name� o� th� file� wher� t� sav� �th� �
circui� �descriptio� (.ci� file� an� th� ne�-lis� �(.ne� �file)� �
Afte� this� an� progra� ca� b� execute� whil� th� edito� remain� �
residen� �i� memory� wit� executio� returnin� late� t� th� �ed��
tor� 

A� importan� featur� o� th� progra� i� th� optiona� us� o� �fo��
mula� i� th� parameters� An� mathematica� expressio� usin� con��
tant� an� value� give� i� � valu� lis� ca� b� use� fo� � numer��
ca� �parameter� �Th� expression� ar� evaluate� i� �th� �ne�-lis� �
generation� Thi� allow� eas� us� o� componen� valu� list� �gen��
rate� b� synthesi� programs� o� eve� th� us� o� EdFi� a� � �sy��
thesi� �program� �wit� component� parameter� �give� �b� �projec� �
formulae� �Th� �"=� sig� ca� b� use� i� formula� t� �creat� �ne� �
value� i� th� valu� list� Us� resistor� wit� bot� node� grounde� �
t� creat� set� o� value� i� thi� way� an� operat� th� progra� a� �
� simpl� spreadsheet� Evaluatio� i� fro� botto� t� top� lef� �t� �
right.

Th� �defaul� scree� mod� selectio� ca� b� overridde� a� �i� �th� �
IFF� �program� �Th� .BG� file� mus� b� presen� �o� �th� �defaul� �
driv� o� i� th� pat� indicate� b� th� DO� variabl� TPGBI.

Contactin� th� author:�----------------------

Comment� �an� �doubt� abou� th� program� shal� b� �sen� �t� �th� �
author:

Dr. Antonio Carlos M. de Queiroz
Programa de Engenharia Eletrica - COPPE
Universidade Federal do Rio de Janeiro
CP 68504
21945-970 Rio de Janeiro, RJ, Brazil
E-mail: acmq@coe.ufrj.b�
FTP� coe.ufrj.br� director� pub/acmq
WWW� http://www.coe.ufrj.br/gpas/acmq.html 

Files on the distributio� compresse� file:
------------------------------------------

IFFT-1.EXE: Rea� mod� version (an� PC).
IFFT.EXE� Protecte� mod� versio� (38� up� 10� references).
EDFIL.EXE: Circuit editor program.
*.BGI: Graphics drivers.
LITT.CHR: Font for the messages window.
*.CIR: Circuit files em EdFil format.
*.NET: NetList files.
*.VAL: Value list files for EdFil.
*.TXT� Documentation.
RTM.EXE� DPMI16BI.OVL� Protecte� mod� drivers.

Licensing
---------

Th� IFF� progra� ca� b� use� an� distribute� fre� o� charge� fo� �
educationa� purposes� a� lon� a� i� i� no� changed� an� referen�
c� i� mad� i� an� wor� don� wit� it� help� Al� othe� right� �ar� �
reserved� Fo� commercia� uses� contac� th� author.

Th� autho� believe� tha� th� progra� work� correctly� bu� canno� �
b� �responsibl� �fo� �an� losse� du� t� �possibl� �bug� �i� �th� �
progra� tha� escape� hi� attention.

User� �ar� encourage� t� sen� t� th� autho� � lette� �o� ��-mai� �
messag� �tellin� wher� th� progra� i� bein� used� an� �fo� �wha� �
purpose.

Versio� information
-------------------

Versio� 1.3b� � bu� i� th� inclusio� o� amplifier� i� th� norma� �
tre� wa� corrected.
Versio� 1.3a� � bu� i� Gd� i� th� MO� transisto� wa� corrected.
Versio� �1.3� �Complexit� orde� estimatio� improve� �b� �� �mor� �
genera� �algorith� �fo� th� generatio� o� th� norma� �tree� �Th� �
progra� �wil� no� anymor� underestimat� th� order� �Mont� �Carl� �
analysi� introduced.
�ACMQ - 17 October 1996
