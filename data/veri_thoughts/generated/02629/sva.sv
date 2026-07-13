module my_module_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic out1
);
    // Combinational RTL; no reset/clock in DUT; assertions are sampled on clk.

    // out1 equals (in1 & in2 & in3 & in4) | in5.
    check_out1_equation: assert property (
        @(posedge clk) out1 == ((in1 & in2 & in3 & in4) | in5)
    );

    // in5 high forces out1 high.
    check_in5_forces_out1: assert property (
        @(posedge clk) in5 |-> out1
    );

    // When in5 is low, out1 equals in1&in2&in3&in4.
    check_out1_when_in5_low: assert property (
        @(posedge clk) !in5 |-> (out1 == (in1 & in2 & in3 & in4))
    );

    // All of in1..in4 high implies out1 high.
    check_all_in_high_implies_out1_high: assert property (
        @(posedge clk) (in1 & in2 & in3 & in4) |-> out1
    );

    // With in5 low and any of in1..in4 low, out1 must be low.
    check_any_in_low_with_in5_low_implies_out1_low: assert property (
        @(posedge clk) (!in5 && !(in1 & in2 & in3 & in4)) |-> !out1
    );

    // If inputs are stable, out1 must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({in1,in2,in3,in4,in5}) |-> $stable(out1)
    );

    // out1 low implies in5 is low and not(all of in1..in4 are high).
    check_out1_low_implies_inputs: assert property (
        @(posedge clk) !out1 |-> (!in5 && !(in1 & in2 & in3 & in4))
    );

    // If out1 is high while in5 is low, then all of in1..in4 must be high.
    check_out1_high_with_in5_low_implies_all_in_high: assert property (
        @(posedge clk) (out1 && !in5) |-> (in1 && in2 && in3 && in4)
    );
endmodule