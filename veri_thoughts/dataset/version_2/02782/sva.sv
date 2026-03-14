module ddr3_s4_uniphy_example_if0_p0_hr_to_fr_sva (
    input logic clk,
    input logic d_h0,
    input logic d_h1,
    input logic d_l0,
    input logic d_l1,
    input logic q0,
    input logic q1
);
    // q0 reflects d_l0 sampled on previous posedge (low-phase path).
    map_q0_from_d_l0_on_posedge: assert property (
        @(posedge clk) disable iff ($initstate) q0 == $past(d_l0)
    );
    // q1 reflects d_l1 sampled on previous posedge (low-phase path).
    map_q1_from_d_l1_on_posedge: assert property (
        @(posedge clk) disable iff ($initstate) q1 == $past(d_l1)
    );
    // q0 reflects d_h0 sampled at the most recent posedge when clk falls (high-phase path).
    map_q0_from_d_h0_on_negedge: assert property (
        @(negedge clk) disable iff ($initstate) q0 == $past(d_h0, 0, posedge clk)
    );
    // q1 reflects d_h1 sampled at the most recent posedge when clk falls (high-phase path).
    map_q1_from_d_h1_on_negedge: assert property (
        @(negedge clk) disable iff ($initstate) q1 == $past(d_h1, 0, posedge clk)
    );
endmodule