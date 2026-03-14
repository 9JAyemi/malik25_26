module priority_encoder_sva (
    input logic clk,
    input logic [1:0] in,
    input logic [1:0] out
);
    // Combinational DUT with no reset; use clk only for sampling.

    // Output equals input every sampled cycle.
    check_out_equals_in: assert property (
        @(posedge clk) out == in
    );

    // For in==00, out must be 00.
    check_case_00: assert property (
        @(posedge clk) (in == 2'b00) |-> (out == 2'b00)
    );

    // For in==01, out must be 01.
    check_case_01: assert property (
        @(posedge clk) (in == 2'b01) |-> (out == 2'b01)
    );

    // For in==10, out must be 10.
    check_case_10: assert property (
        @(posedge clk) (in == 2'b10) |-> (out == 2'b10)
    );

    // For in==11, out must be 11.
    check_case_11: assert property (
        @(posedge clk) (in == 2'b11) |-> (out == 2'b11)
    );

    // If input is stable across cycles, output is stable.
    check_stability_when_input_stable: assert property (
        @(posedge clk) (in == $past(in)) |-> (out == $past(out))
    );

    // Output change across cycles implies input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(out) |-> $changed(in)
    );

    // Input change across cycles implies output changed.
    check_input_change_implies_output_change: assert property (
        @(posedge clk) $changed(in) |-> $changed(out)
    );
endmodule