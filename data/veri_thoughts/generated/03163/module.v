module tkg_ao222 (output o, input i0, i1, i2, i3, i4, i5);
	AO222 I0 (o, i0, i1, i2, i3, i4, i5);
endmodule

module AO222 (output o, input i0, i1, i2, i3, i4, i5);
	assign o = i0 & i1 & i2 | i3 & i4 & i5;
endmodule