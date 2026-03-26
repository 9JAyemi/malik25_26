


module jt12_sh24 #(parameter width=5 )
(
  input 	clk,
  input   clk_en ,  
  input		[width-1:0]	din,
 	output reg [width-1:0]	st1,
 	output reg [width-1:0]	st2,
 	output reg [width-1:0]	st3,
 	output reg [width-1:0]	st4,
 	output reg [width-1:0]	st5,
 	output reg [width-1:0]	st6,
 	output reg [width-1:0]	st7,
 	output reg [width-1:0]	st8,
 	output reg [width-1:0]	st9,
 	output reg [width-1:0]	st10,
 	output reg [width-1:0]	st11,
 	output reg [width-1:0]	st12,
 	output reg [width-1:0]	st13,
 	output reg [width-1:0]	st14,
 	output reg [width-1:0]	st15,
 	output reg [width-1:0]	st16,
 	output reg [width-1:0]	st17,
 	output reg [width-1:0]	st18,
 	output reg [width-1:0]	st19,
 	output reg [width-1:0]	st20,
 	output reg [width-1:0]	st21,
 	output reg [width-1:0]	st22,
 	output reg [width-1:0]	st23,
 	output reg [width-1:0]	st24
);

always @(posedge clk) if(clk_en) begin
	st24<= st23;
	st23<= st22;
	st22<= st21;
	st21<= st20;
	st20<= st19;
	st19<= st18;
	st18<= st17;
	st17<= st16;
	st16<= st15;
	st15<= st14;
	st14<= st13;
	st13<= st12;
	st12<= st11;
	st11<= st10;
	st10<= st9;
	st9 <= st8;
	st8 <= st7;
	st7 <= st6;
	st6 <= st5;
	st5 <= st4;
	st4 <= st3;
	st3 <= st2;
	st2 <= st1;
	st1 <= din;
end

endmodule
