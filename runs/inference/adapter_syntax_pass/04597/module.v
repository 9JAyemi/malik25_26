
module mux_2_1(input sel, input in0, input in1, output out);
    wire not_sel;
    wire and_0;
    wire and_1;

    not (not_sel, sel);

    and (and_0, in0, not_sel);

    and (and_1, in1, sel);

    assign out = and_0 | and_1;
endmodule
