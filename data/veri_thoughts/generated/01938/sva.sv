module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic [7:0] q
);
    // q equals zero-extended selected input bit.
    check_q_zeroext_selected: assert property (
        @(posedge clk) disable iff (reset) q == {7'b0, in[sel]}
    );

    // Upper bits of q are always zero.
    check_q_upper_bits_zero: assert property (
        @(posedge clk) disable iff (reset) q[7:1] == 7'b0
    );

    // When sel==00, q reflects in[0] in LSB and zeros elsewhere.
    check_sel00_behavior: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b00) |-> (q == {7'b0, in[0]})
    );

    // When sel==01, q reflects in[1] in LSB and zeros elsewhere.
    check_sel01_behavior: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b01) |-> (q == {7'b0, in[1]})
    );

    // When sel==10, q reflects in[2] in LSB and zeros elsewhere.
    check_sel10_behavior: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b10) |-> (q == {7'b0, in[2]})
    );

    // When sel==11, q reflects in[3] in LSB and zeros elsewhere.
    check_sel11_behavior: assert property (
        @(posedge clk) disable iff (reset) (sel == 2'b11) |-> (q == {7'b0, in[3]})
    );

    // If all inputs are zero, q must be zero regardless of sel.
    check_all_inputs_zero: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b0000) |-> (q == 8'h00)
    );

    // If all inputs are one, q must be one regardless of sel.
    check_all_inputs_one: assert property (
        @(posedge clk) disable iff (reset) (in == 4'b1111) |-> (q == 8'h01)
    );

    // q is always either 0 or 1.
    check_q_value_range: assert property (
        @(posedge clk) disable iff (reset) (q inside {8'h00, 8'h01})
    );
endmodule