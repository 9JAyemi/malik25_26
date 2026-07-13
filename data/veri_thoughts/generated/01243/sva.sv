module decoder_sva (
    input logic [6:0] address,
    input logic bar_led_ce_n,
    input logic board_led_ce_n,
    input logic switch_ce_n,
    input logic mem1_ce_n,
    input logic mem2_ce_n
);
    // No explicit clock/reset in RTL; sample assertions on a data edge.
    ///// Decode equivalences /////
    // switch_ce_n low iff address == 7'h74.
    eq_switch_decode: assert property (
        @(posedge address[0]) (switch_ce_n == (address != 7'h74))
    );
    // bar_led_ce_n low iff address == 7'h6C.
    eq_bar_led_decode: assert property (
        @(posedge address[0]) (bar_led_ce_n == (address != 7'h6C))
    );
    // board_led_ce_n low iff address == 7'h2F.
    eq_board_led_decode: assert property (
        @(posedge address[0]) (board_led_ce_n == (address != 7'h2F))
    );
    // mem1_ce_n low iff address[6:4] == 3'b000 (0x00-0x0F).
    eq_mem1_decode: assert property (
        @(posedge address[0]) (mem1_ce_n == (address[6:4] != 3'b000))
    );
    // mem2_ce_n low iff address[6:4] == 3'b101 (0x50-0x5F).
    eq_mem2_decode: assert property (
        @(posedge address[0]) (mem2_ce_n == (address[6:4] != 3'b101))
    );
    ///// Mutual exclusion /////
    // At most one active-low CE is asserted at a time.
    at_most_one_active: assert property (
        @(posedge address[0]) $onehot0({~bar_led_ce_n, ~board_led_ce_n, ~switch_ce_n, ~mem1_ce_n, ~mem2_ce_n})
    );
    ///// Default behavior /////
    // If no decode matches, all CEs remain deasserted (HIGH).
    default_no_match_all_high: assert property (
        @(posedge address[0])
        ((address != 7'h74) && (address != 7'h6C) && (address != 7'h2F) &&
         (address[6:4] != 3'b000) && (address[6:4] != 3'b101))
        |-> (switch_ce_n && bar_led_ce_n && board_led_ce_n && mem1_ce_n && mem2_ce_n)
    );
    ///// Specific address exclusivity /////
    // At address 7'h74 only switch_ce_n is asserted (LOW).
    only_switch_on_0x74: assert property (
        @(posedge address[0]) (address == 7'h74)
        |-> (!switch_ce_n && bar_led_ce_n && board_led_ce_n && mem1_ce_n && mem2_ce_n)
    );
    // At address 7'h6C only bar_led_ce_n is asserted (LOW).
    only_bar_led_on_0x6C: assert property (
        @(posedge address[0]) (address == 7'h6C)
        |-> (!bar_led_ce_n && switch_ce_n && board_led_ce_n && mem1_ce_n && mem2_ce_n)
    );
    // At address 7'h2F only board_led_ce_n is asserted (LOW).
    only_board_led_on_0x2F: assert property (
        @(posedge address[0]) (address == 7'h2F)
        |-> (!board_led_ce_n && switch_ce_n && bar_led_ce_n && mem1_ce_n && mem2_ce_n)
    );
endmodule