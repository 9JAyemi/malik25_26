

module full_adder_1bit_struct
  (

   input                     Ain,
   input                     Bin,
   input                     Cin,

   output                    Sum,
   output                    Cout
  );

  assign Sum  = Ain ^ Bin ^ Cin;
  assign Cout = (Ain & Bin) | (Bin & Cin) | (Cin & Ain);

endmodule module full_sub_1bit_struct
  (

   input                     Xin,
   input                     Yin,
   input                     BorrowIn,

   output                    Diff,
   output                    BorrowOut 
  );

  assign Diff      = Xin ^ Yin ^ BorrowIn;
  assign BorrowOut = (~Xin & Yin) | (~Xin & BorrowIn) | (Yin & BorrowIn);

endmodule module parity_gen_1bit_struct
  (

   input                     Ain,
   input                     Bin,

   output                    ParityOut 
  );

  assign ParityOut = (~Ain & Bin) | (Ain & ~Bin);

endmodule module comparator_1bit_struct
  (

   input                     Ain,
   input                     Bin,

   output                    CompOut 
  );

  assign CompOut = (~Ain & ~Bin) | (Ain & Bin);

endmodule module full_adder_generic(Ain, Bin, Cin, Sum, Cout);

  parameter WIDTH = 2;

  input [WIDTH-1:0] Ain;
  input [WIDTH-1:0] Bin;
  input             Cin;

  output [WIDTH-1:0] Sum;
  output             Cout;

  wire [WIDTH:0] temp_cout;

  assign temp_cout[0] = Cin;

  generate
     genvar i;
     for (i=0; i<WIDTH; i=i+1) begin: ADDER
         full_adder_1bit_struct FA_1bit(
            .Ain (Ain[i]),
            .Bin (Bin[i]),
            .Cin (temp_cout[i]),
            .Sum  (Sum[i]),
            .Cout (temp_cout[i+1])
         );
     end
  endgenerate

  assign Cout = temp_cout[WIDTH];

endmodule module full_sub_generic(Xin, Yin, BorrowIn, Diff, BorrowOut);

  parameter WIDTH = 2;

  input [WIDTH-1:0] Xin;
  input [WIDTH-1:0] Yin;
  input             BorrowIn;

  output [WIDTH-1:0] Diff;
  output             BorrowOut;

  wire [WIDTH:0] temp_borrow;

  assign temp_borrow[0] = BorrowIn;

  generate
     genvar i;
     for (i=0; i<WIDTH; i=i+1) begin: ADDER
         full_sub_1bit_struct SUB_1bit(
            .Xin       (Xin[i]),
            .Yin       (Yin[i]),
            .BorrowIn  (temp_borrow[i]),
            .Diff      (Diff[i]),
            .BorrowOut (temp_borrow[i+1])
         );
     end
  endgenerate

  assign BorrowOut = temp_borrow[WIDTH];

endmodule module parity_gen_generic(Ain, Bin, ParityOut);

  parameter WIDTH = 2;

  input [WIDTH-1:0] Ain;
  input [WIDTH-1:0] Bin;

  output [WIDTH-1:0] ParityOut;

  wire [WIDTH-1:0] temp_pout;

  generate
     genvar i;
     for (i=0; i<WIDTH; i=i+1) begin: PARITY
         parity_gen_1bit_struct PARITY_1bit(
            .Ain        (Ain[i]),
            .Bin        (Bin[i]),
            .ParityOut  (temp_pout[i])
         );
     end
  endgenerate

  assign ParityOut = temp_pout;

endmodule module comparator_generic(Ain, Bin, CompOut);

  parameter WIDTH = 2;

  input [WIDTH-1:0] Ain;
  input [WIDTH-1:0] Bin;

  output [WIDTH-1:0] CompOut;

  wire [WIDTH-1:0] temp_cout;

  generate
     genvar i;
     for (i=0; i<WIDTH; i=i+1) begin: COMPARATOR
         comparator_1bit_struct COMPARATOR_1bit(
            .Ain        (Ain[i]),
            .Bin        (Bin[i]),
            .CompOut  (temp_cout[i])
         );
     end
  endgenerate

  assign CompOut = temp_cout;

endmodule 