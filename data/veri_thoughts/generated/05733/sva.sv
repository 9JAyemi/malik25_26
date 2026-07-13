module axi_ethernet_ram_reader_sva (
    input logic state1a,
    input logic goto_readDestAdrNib1,
    input logic state0a,
    input logic out_1,
    input logic ram_valid_i,
    input logic s_axi_aclk,
    input logic [0:0] AR,
    input logic startReadDestAdrNib,
    input logic [7:0] Q
);

    // goto_readDestAdrNib1 is the same decode as state1a.
    check_goto_matches_state1a: assert property (
        @(posedge s_axi_aclk) goto_readDestAdrNib1 == state1a
    );

    // The two exported state decodes are never high together.
    check_state_decodes_mutex: assert property (
        @(posedge s_axi_aclk) !(state1a && state0a)
    );

    // out_1 matches the combinational definition from state0a and ram_valid_i.
    check_out1_definition: assert property (
        @(posedge s_axi_aclk) out_1 == (state0a && ram_valid_i)
    );

    // In state0a, ram_valid_i drives a transition to state1a on the next cycle.
    check_idle_to_state1_on_ram_valid: assert property (
        @(posedge s_axi_aclk) (state0a && ram_valid_i) |=> state1a
    );

    // In state0a without ram_valid_i, the state stays in state0a.
    check_idle_holds_without_ram_valid: assert property (
        @(posedge s_axi_aclk) (state0a && !ram_valid_i) |=> state0a
    );

    // In state1a with startReadDestAdrNib low, the next cycle returns to state0a.
    check_state1_to_state0_when_start_low: assert property (
        @(posedge s_axi_aclk) (state1a && !startReadDestAdrNib) |=> state0a
    );

    // In state1a with startReadDestAdrNib high, the state remains state1a.
    check_state1_holds_when_start_high: assert property (
        @(posedge s_axi_aclk) (state1a && startReadDestAdrNib) |=> state1a
    );

    // out_1 can only be high while the exported state decode is state0a.
    check_out1_only_in_state0: assert property (
        @(posedge s_axi_aclk) out_1 |-> state0a
    );

    // out_1 implies the machine will be in state1a on the next cycle.
    check_out1_leads_to_state1: assert property (
        @(posedge s_axi_aclk) out_1 |=> state1a
    );

endmodule