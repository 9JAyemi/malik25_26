module axi_timer_sva (
    input logic [4:0] bus2ip_addr_i_reg,
    input logic Q,
    input logic ce_expnd_i_5
);
    ///// Combinational truth table checks (sampled on input edges) /////
    // When Q is HIGH, ce_expnd_i_5 must be LOW for all address values.
    check_q_high_forces_zero: assert property (
        @(posedge Q) ce_expnd_i_5 == 1'b0
    );

    // When addr[1] rises (addr[1]==1), ce_expnd_i_5 must be LOW.
    check_addr1_high_forces_zero: assert property (
        @(posedge bus2ip_addr_i_reg[1]) ce_expnd_i_5 == 1'b0
    );

    // When addr[0] rises (addr[0]==1), ce_expnd_i_5 must be LOW.
    check_addr0_high_forces_zero: assert property (
        @(posedge bus2ip_addr_i_reg[0]) ce_expnd_i_5 == 1'b0
    );

    // Functional equivalence sampled on addr[2] edge: ce = addr[2] & ~Q & ~addr[1] & ~addr[0].
    check_function_on_addr2_edge: assert property (
        @(posedge bus2ip_addr_i_reg[2])
            ce_expnd_i_5 == (bus2ip_addr_i_reg[2] && !Q && !bus2ip_addr_i_reg[1] && !bus2ip_addr_i_reg[0])
    );

    // Functional equivalence sampled on addr[3] edge (addr[3] is don't-care in RTL).
    check_function_on_addr3_edge: assert property (
        @(posedge bus2ip_addr_i_reg[3])
            ce_expnd_i_5 == (bus2ip_addr_i_reg[2] && !Q && !bus2ip_addr_i_reg[1] && !bus2ip_addr_i_reg[0])
    );

    // Functional equivalence sampled on addr[4] edge (addr[4] is don't-care in RTL).
    check_function_on_addr4_edge: assert property (
        @(posedge bus2ip_addr_i_reg[4])
            ce_expnd_i_5 == (bus2ip_addr_i_reg[2] && !Q && !bus2ip_addr_i_reg[1] && !bus2ip_addr_i_reg[0])
    );

    // If addr[2]==1, Q==0, and addr[1:0]==2'b00, output must be HIGH.
    check_unique_high_condition_sufficient: assert property (
        @(posedge bus2ip_addr_i_reg[2])
            ((bus2ip_addr_i_reg[2] && !Q && !bus2ip_addr_i_reg[1] && !bus2ip_addr_i_reg[0]) |-> (ce_expnd_i_5 == 1'b1))
    );

    // If output is HIGH, then addr[2]==1, Q==0, and addr[1:0]==2'b00 must hold.
    check_unique_high_condition_necessary: assert property (
        @(posedge bus2ip_addr_i_reg[2])
            (ce_expnd_i_5 == 1'b1 |-> (bus2ip_addr_i_reg[2] && !Q && !bus2ip_addr_i_reg[1] && !bus2ip_addr_i_reg[0]))
    );

    // With addr[2]==1, any disqualifier (Q or addr[1] or addr[0]) HIGH forces output LOW.
    check_disqualifiers_force_zero_on_addr2: assert property (
        @(posedge bus2ip_addr_i_reg[2])
            (((Q == 1'b1) || (bus2ip_addr_i_reg[1] == 1'b1) || (bus2ip_addr_i_reg[0] == 1'b1)) |-> (ce_expnd_i_5 == 1'b0))
    );
endmodule