
module half_adder (
    input a,
    input b,
    output sum,
    output carry_out
);
    assign sum = a ^ b;
    assign carry_out = a & b;
endmodule

module two_to_one_mux (
    input sel1,
    input sel2,
    input in1,
    input in2,
    output out_mux
);
    wire temp;
    assign temp = sel1 & sel2 ? in1 : in2;
    assign out_mux = temp;
endmodule

module final_module (
    input sum,
    input carry_out,
    output out_final
);
    assign out_final = sum ^ carry_out;
endmodule

module top_module (
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    output out_always
);
    wire sum, carry_out;
    half_adder ha_inst(
        .a(a),
        .b(b),
        .sum(sum),
        .carry_out(carry_out)
    );
    wire mux_input1, mux_input2;
    assign mux_input1 = sum;
    assign mux_input2 = carry_out;
    wire final_input;
    final_module fm_inst(
        .sum(sum),
        .carry_out(carry_out),
        .out_final(final_input)
    );
    two_to_one_mux mux_inst(
        .sel1(sel_b1),
        .sel2(sel_b2),
        .in1(mux_input1),
        .in2(mux_input2),
        .out_mux(out_always)
    );
endmodule
