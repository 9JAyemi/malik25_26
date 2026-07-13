module ddr3_s4_uniphy_p0_hr_to_fr_sva (
    input logic clk,
    input logic d_h0,
    input logic d_h1,
    input logic d_l0,
    input logic d_l1,
    input logic q0,
    input logic q1
);

    property p_q0_from_d_h0;
        logic sampled_d_h0;
        @(posedge clk)
            (1'b1, sampled_d_h0 = d_h0) |=> (q0 == sampled_d_h0);
    endproperty

    property p_q1_from_d_h1;
        logic sampled_d_h1;
        @(posedge clk)
            (1'b1, sampled_d_h1 = d_h1) |=> (q1 == sampled_d_h1);
    endproperty

    property p_q0_from_d_l0;
        logic sampled_d_l0;
        @(posedge clk)
            (1'b1, sampled_d_l0 = d_l0) |=> @(negedge clk) (q0 == sampled_d_l0);
    endproperty

    property p_q1_from_d_l1;
        logic sampled_d_l1;
        @(posedge clk)
            (1'b1, sampled_d_l1 = d_l1) |=> @(negedge clk) (q1 == sampled_d_l1);
    endproperty

    // q0 shows the prior captured d_h0 value at the next posedge sample.
    check_q0_from_d_h0: assert property (p_q0_from_d_h0);

    // q1 shows the prior captured d_h1 value at the next posedge sample.
    check_q1_from_d_h1: assert property (p_q1_from_d_h1);

    // q0 shows the captured d_l0 value at the following high-phase negedge sample.
    check_q0_from_d_l0: assert property (p_q0_from_d_l0);

    // q1 shows the captured d_l1 value at the following high-phase negedge sample.
    check_q1_from_d_l1: assert property (p_q1_from_d_l1);

endmodule