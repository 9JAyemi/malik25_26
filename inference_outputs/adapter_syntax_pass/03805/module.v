
module Test6(input OE, inout [3:0] Z10);
   wire [1:0] i;
   Test6a a (.OE(OE), .Z({Z10[1],Z10[0]})); // Z10[0] and Z10[1] swapped
   Test6a b (.OE(~OE), .Z({Z10[3],Z10[2]})); // Z10[2] and Z10[3] swapped
endmodule

module Test6a(input OE, inout [1:0] Z);
   assign Z = OE ? 2'b10 : 2'b01;
endmodule
