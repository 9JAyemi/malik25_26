module delay_module (
    input g,
    input d,
    input s,
    output reg out
);

wire d_delayed;

Four_PMOS_delay delay_inst (
    .delay_enable(g),
    .data(d),
    .q(d_delayed)
);

always @(*) begin
    out = (s == 1'b1) ? ~d_delayed : d_delayed;
end

endmodule 

module Four_PMOS_delay (
    input delay_enable,
    input data,
    output reg q
);

always @(*) begin
    if (delay_enable)
        q <= #100 data;
end

endmodule