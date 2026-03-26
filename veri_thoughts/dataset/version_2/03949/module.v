module decoders38(in, out, en);
	input [0:2]in;
	input [0:2]en;
	output [0:7]out;
	wire enableWire;
	
	and
	andGateEnable(enableWire, en[0], ~en[1], ~en[2]);
	
	nand 
	nandGate0(out[0], ~in[2], ~in[1], ~in[0], enableWire),
	nandGate1(out[1], ~in[2], ~in[1], in[0], enableWire),
	nandGate2(out[2], ~in[2], in[1], ~in[0], enableWire),
	nandGate3(out[3], ~in[2], in[1], in[0], enableWire),
	nandGate4(out[4], in[2], ~in[1], ~in[0], enableWire),
	nandGate5(out[5], in[2], ~in[1], in[0], enableWire),
	nandGate6(out[6], in[2], in[1], ~in[0], enableWire),
	nandGate7(out[7], in[2], in[1], in[0], enableWire);
endmodule
