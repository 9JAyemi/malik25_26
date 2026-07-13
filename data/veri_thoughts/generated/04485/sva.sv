module edge_detector_pipeline_sva (
    input logic       clk,
    input logic [7:0] in,
    input logic [7:0] anyedge,
    input logic [7:0] reg1,
    input logic [7:0] reg2,
    input logic [7:0] reg3,
    input logic [7:0] reg4,
    input logic [7:0] reg5,
    input logic [7:0] reg6,
    input logic [7:0] reg7,
    input logic [7:0] reg8
);

    // reg1 captures in on the next clock.
    property p_reg1_captures_in;
        logic [7:0] sampled_in;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_in = in) |=> (reg1 == sampled_in);
    endproperty
    check_reg1_captures_in: assert property (p_reg1_captures_in);

    // reg2 captures reg1 on the next clock.
    property p_reg2_captures_reg1;
        logic [7:0] sampled_reg1;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg1 = reg1) |=> (reg2 == sampled_reg1);
    endproperty
    check_reg2_captures_reg1: assert property (p_reg2_captures_reg1);

    // reg3 captures reg2 on the next clock.
    property p_reg3_captures_reg2;
        logic [7:0] sampled_reg2;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg2 = reg2) |=> (reg3 == sampled_reg2);
    endproperty
    check_reg3_captures_reg2: assert property (p_reg3_captures_reg2);

    // reg4 captures reg3 on the next clock.
    property p_reg4_captures_reg3;
        logic [7:0] sampled_reg3;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg3 = reg3) |=> (reg4 == sampled_reg3);
    endproperty
    check_reg4_captures_reg3: assert property (p_reg4_captures_reg3);

    // reg5 captures reg4 on the next clock.
    property p_reg5_captures_reg4;
        logic [7:0] sampled_reg4;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg4 = reg4) |=> (reg5 == sampled_reg4);
    endproperty
    check_reg5_captures_reg4: assert property (p_reg5_captures_reg4);

    // reg6 captures reg5 on the next clock.
    property p_reg6_captures_reg5;
        logic [7:0] sampled_reg5;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg5 = reg5) |=> (reg6 == sampled_reg5);
    endproperty
    check_reg6_captures_reg5: assert property (p_reg6_captures_reg5);

    // reg7 captures reg6 on the next clock.
    property p_reg7_captures_reg6;
        logic [7:0] sampled_reg6;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg6 = reg6) |=> (reg7 == sampled_reg6);
    endproperty
    check_reg7_captures_reg6: assert property (p_reg7_captures_reg6);

    // reg8 captures reg7 on the next clock.
    property p_reg8_captures_reg7;
        logic [7:0] sampled_reg7;
        @(posedge clk) disable iff (1'b0)
            (1'b1, sampled_reg7 = reg7) |=> (reg8 == sampled_reg7);
    endproperty
    check_reg8_captures_reg7: assert property (p_reg8_captures_reg7);

    // anyedge matches the implemented XOR and delay logic.
    property p_anyedge_definition;
        @(posedge clk) disable iff (1'b0)
            (anyedge == {
                reg8[7],
                (reg7[6] ^ reg8[6]),
                (reg6[5] ^ reg7[5]),
                (reg5[4] ^ reg6[4]),
                (reg4[3] ^ reg5[3]),
                (reg3[2] ^ reg4[2]),
                (reg2[1] ^ reg3[1]),
                (reg1[0] ^ reg2[0])
            });
    endproperty
    check_anyedge_definition: assert property (p_anyedge_definition);

endmodule

bind edge_detector_pipeline edge_detector_pipeline_sva edge_detector_pipeline_sva_i (
    .clk(clk),
    .in(in),
    .anyedge(anyedge),
    .reg1(reg1),
    .reg2(reg2),
    .reg3(reg3),
    .reg4(reg4),
    .reg5(reg5),
    .reg6(reg6),
    .reg7(reg7),
    .reg8(reg8)
);