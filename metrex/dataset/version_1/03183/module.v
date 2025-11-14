module bt (
   out,
   in
   );
   input [7:0] in;
   output [7:0] out;

   wire [7:0] 	out = ~in;
endmodule module top (
   outgo,
   incom
   );
   input [31:0] incom;
   output [31:0] outgo;

   

   bt BT0 (
	   .out				(outgo[7:0]),		 .in				(incom[7:0]));		 bt BT1 (
	   .out				(outgo[15:8]),		 .in				(incom[15:8]));		 bt BT2 (
	   .out				(outgo[23:16]),		 .in				(incom[23:16]));		 bt BT3 (
	   .out				(outgo[31:24]),		 .in				(incom[31:24]));		 endmodule 