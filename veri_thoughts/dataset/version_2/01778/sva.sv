module system_axi_quad_spi_shield_0_axi_lite_ipif_v3_0_4_pselect_f__parameterized4_sva (
    input logic p_11_out,
    input logic [4:0] bus2ip_addr_i_reg,
    input logic Q
);
    // Combinational decode; sample on any input edge.
    // Output equals the specified AND of inputs.
    check_definitional_equivalence: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        p_11_out == (bus2ip_addr_i_reg[2] & ~bus2ip_addr_i_reg[0] & bus2ip_addr_i_reg[4] & Q & ~bus2ip_addr_i_reg[3] & bus2ip_addr_i_reg[1])
    );

    // If output is HIGH, all required input conditions must hold.
    check_out_high_requires_inputs: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        p_11_out |-> (Q
                      && (bus2ip_addr_i_reg[2] == 1'b1)
                      && (bus2ip_addr_i_reg[4] == 1'b1)
                      && (bus2ip_addr_i_reg[1] == 1'b1)
                      && (bus2ip_addr_i_reg[0] == 1'b0)
                      && (bus2ip_addr_i_reg[3] == 1'b0))
    );

    // Q low forces output low.
    check_q_low_forces_low: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        (Q == 1'b0) |-> (p_11_out == 1'b0)
    );

    // bus2ip_addr_i_reg[0] high forces output low.
    check_bus0_one_forces_low: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        (bus2ip_addr_i_reg[0] == 1'b1) |-> (p_11_out == 1'b0)
    );

    // bus2ip_addr_i_reg[3] high forces output low.
    check_bus3_one_forces_low: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        (bus2ip_addr_i_reg[3] == 1'b1) |-> (p_11_out == 1'b0)
    );

    // bus2ip_addr_i_reg[1] low forces output low.
    check_bus1_zero_forces_low: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        (bus2ip_addr_i_reg[1] == 1'b0) |-> (p_11_out == 1'b0)
    );

    // bus2ip_addr_i_reg[2] low forces output low.
    check_bus2_zero_forces_low: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        (bus2ip_addr_i_reg[2] == 1'b0) |-> (p_11_out == 1'b0)
    );

    // bus2ip_addr_i_reg[4] low forces output low.
    check_bus4_zero_forces_low: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        (bus2ip_addr_i_reg[4] == 1'b0) |-> (p_11_out == 1'b0)
    );

    // When address bits match the decode pattern, output equals Q.
    check_pattern_implies_q_passthrough: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        ((bus2ip_addr_i_reg[2] == 1'b1)
         && (bus2ip_addr_i_reg[4] == 1'b1)
         && (bus2ip_addr_i_reg[1] == 1'b1)
         && (bus2ip_addr_i_reg[0] == 1'b0)
         && (bus2ip_addr_i_reg[3] == 1'b0)) |-> (p_11_out == Q)
    );

    // Under the decode pattern, a rising Q causes a rising output.
    check_q_rise_propagates_under_pattern: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        ($rose(Q)
         && (bus2ip_addr_i_reg[2] == 1'b1)
         && (bus2ip_addr_i_reg[4] == 1'b1)
         && (bus2ip_addr_i_reg[1] == 1'b1)
         && (bus2ip_addr_i_reg[0] == 1'b0)
         && (bus2ip_addr_i_reg[3] == 1'b0)) |-> $rose(p_11_out)
    );

    // Under the decode pattern, a falling Q causes a falling output.
    check_q_fall_propagates_under_pattern: assert property (
        @(posedge Q or negedge Q
          or posedge bus2ip_addr_i_reg[0] or negedge bus2ip_addr_i_reg[0]
          or posedge bus2ip_addr_i_reg[1] or negedge bus2ip_addr_i_reg[1]
          or posedge bus2ip_addr_i_reg[2] or negedge bus2ip_addr_i_reg[2]
          or posedge bus2ip_addr_i_reg[3] or negedge bus2ip_addr_i_reg[3]
          or posedge bus2ip_addr_i_reg[4] or negedge bus2ip_addr_i_reg[4])
        ($fell(Q)
         && (bus2ip_addr_i_reg[2] == 1'b1)
         && (bus2ip_addr_i_reg[4] == 1'b1)
         && (bus2ip_addr_i_reg[1] == 1'b1)
         && (bus2ip_addr_i_reg[0] == 1'b0)
         && (bus2ip_addr_i_reg[3] == 1'b0)) |-> $fell(p_11_out)
    );

endmodule