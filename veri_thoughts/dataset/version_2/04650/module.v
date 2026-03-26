
module ConstantSelection (input SNnotDB, DBnotSN, input [7:0] RomExpConCtl,
                          output Constantb, Constantc, Constantd, Constante,
                          Constantf, Constantg, Constanth);

  wire Func0andDB;
  wire notFunc1;
  wire f0, f1;
  wire Func1, Func0;
  
  assign Func0andDB = RomExpConCtl[2] & DBnotSN;
  assign notFunc1 = ~RomExpConCtl[1];
  assign f0 = RomExpConCtl[0];
  assign f1 = notFunc1 & RomExpConCtl[0];
  assign Func0 = f0 & f1;
  assign Func1 = f1 & RomExpConCtl[1];
  
  assign Constantb = Func1 & Func0 & DBnotSN;
  assign Constantc = Func1 & Func0;
  assign Constantd = Func1;
  assign Constante = Func1 | (Func0 & DBnotSN);
  assign Constantf = Func1 | Func0;
  assign Constantg = Func1 | ~Constanth;
  assign Constanth = ~(~Func1 & Func0 & SNnotDB);
  
endmodule