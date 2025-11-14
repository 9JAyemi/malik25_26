module inverter(
    input din,
    output dout
);

assign dout = ~din;

endmodule