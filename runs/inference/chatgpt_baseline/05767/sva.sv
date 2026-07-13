module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic f,
    input logic xor_out,
    input logic xnor_out,
    input logic [3:0] mux_in
);

    // xor_out captures the previous-cycle XOR of a and b.
    check_xor_registered: assert property (
        @(posedge clk) 1'b1 |=> (xor_out == $past(a ^ b))
    );

    // xnor_out is the current XNOR of a and b.
    check_xnor_function: assert property (
        @(posedge clk) 1'b1 |=> (xnor_out == ~(a ^ b))
    );

    // mux_in[0] and mux_in[1] match their continuous assignments.
    check_mux_data_inputs: assert property (
        @(posedge clk) 1'b1 |=> ((mux_in[0] == (xor_out & xnor_out)) &&
                                 (mux_in[1] == (~xor_out & ~xnor_out)))
    );

    // mux_in[2] and mux_in[3] stay at their constant values.
    check_mux_constant_inputs: assert property (
        @(posedge clk) 1'b1 |=> ((mux_in[2] == 1'b0) &&
                                 (mux_in[3] == 1'b1))
    );

    // f selects mux_in[0] when sel is 2'b00.
    check_mux_sel_00: assert property (
        @(posedge clk) 1'b1 |=> (({xor_out, xnor_out} !== 2'b00) || (f == mux_in[0]))
    );

    // f selects mux_in[1] when sel is 2'b01.
    check_mux_sel_01: assert property (
        @(posedge clk) 1'b1 |=> (({xor_out, xnor_out} !== 2'b01) || (f == mux_in[1]))
    );

    // f selects mux_in[2] when sel is 2'b10.
    check_mux_sel_10: assert property (
        @(posedge clk) 1'b1 |=> (({xor_out, xnor_out} !== 2'b10) || (f == mux_in[2]))
    );

    // f selects mux_in[3] when sel is 2'b11.
    check_mux_sel_11: assert property (
        @(posedge clk) 1'b1 |=> (({xor_out, xnor_out} !== 2'b11) || (f == mux_in[3]))
    );

    // f matches the end-to-end behavior from current and prior input parity.
    check_f_end_to_end: assert property (
        @(posedge clk) 1'b1 |=> (f == ($past(a ^ b) & ~(a ^ b)))
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .f(f),
    .xor_out(xor_out),
    .xnor_out(xnor_out),
    .mux_in(mux_in)
);