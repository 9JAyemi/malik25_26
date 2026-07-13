module CLKSKW_sva (
    input logic       CLKI,
    input logic [3:0] SKW,
    input logic       RST,
    input logic       CLKO,
    input logic [3:0] delay_reg
);

    // A sampled reset leaves both registers cleared at the next clock sample.
    check_state_zero_after_sampled_reset: assert property (
        @(posedge CLKI) disable iff ($initstate)
        $past(RST) |-> ((CLKO == 1'b0) && (delay_reg == 4'b0000))
    );

    // Without a sampled reset, delay_reg shifts in a 1 or is asynchronously cleared to zero.
    check_delay_reg_update_or_async_reset: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        !$past(RST) |-> ((delay_reg == {$past(delay_reg[2:0]), 1'b1}) || (delay_reg == 4'b0000))
    );

    // Any nonzero delay_reg value must have a 1 in bit 0.
    check_nonzero_delay_reg_has_lsb_one: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (delay_reg != 4'b0000) |-> (delay_reg[0] == 1'b1)
    );

    // A cleared delay register also keeps CLKO low.
    check_zero_delay_reg_implies_zero_clko: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (delay_reg == 4'b0000) |-> (CLKO == 1'b0)
    );

    // For SKW=0000, CLKO reflects delay_reg[0] & ~delay_reg[1] from the prior cycle.
    check_clko_skw_0000_select: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (!$past(RST) && ($past(SKW) == 4'b0000)) |->
        (((delay_reg == 4'b0000) && (CLKO == 1'b0)) ||
         (CLKO == ($past(delay_reg[0]) & ~$past(delay_reg[1]))))
    );

    // For SKW=0001, CLKO reflects delay_reg[1] & ~delay_reg[2] from the prior cycle.
    check_clko_skw_0001_select: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (!$past(RST) && ($past(SKW) == 4'b0001)) |->
        (((delay_reg == 4'b0000) && (CLKO == 1'b0)) ||
         (CLKO == ($past(delay_reg[1]) & ~$past(delay_reg[2]))))
    );

    // For SKW=0010, CLKO reflects delay_reg[2] & ~delay_reg[3] from the prior cycle.
    check_clko_skw_0010_select: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (!$past(RST) && ($past(SKW) == 4'b0010)) |->
        (((delay_reg == 4'b0000) && (CLKO == 1'b0)) ||
         (CLKO == ($past(delay_reg[2]) & ~$past(delay_reg[3]))))
    );

    // For SKW=1001, CLKO reflects delay_reg[1] & ~delay_reg[0] from the prior cycle.
    check_clko_skw_1001_select: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (!$past(RST) && ($past(SKW) == 4'b1001)) |->
        (((delay_reg == 4'b0000) && (CLKO == 1'b0)) ||
         (CLKO == ($past(delay_reg[1]) & ~$past(delay_reg[0]))))
    );

    // For SKW=1010, CLKO reflects delay_reg[2] & ~delay_reg[1] from the prior cycle.
    check_clko_skw_1010_select: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (!$past(RST) && ($past(SKW) == 4'b1010)) |->
        (((delay_reg == 4'b0000) && (CLKO == 1'b0)) ||
         (CLKO == ($past(delay_reg[2]) & ~$past(delay_reg[1]))))
    );

    // For SKW=1011, CLKO reflects delay_reg[3] & ~delay_reg[2] from the prior cycle.
    check_clko_skw_1011_select: assert property (
        @(posedge CLKI) disable iff ($initstate || RST)
        (!$past(RST) && ($past(SKW) == 4'b1011)) |->
        (((delay_reg == 4'b0000) && (CLKO == 1'b0)) ||
         (CLKO == ($past(delay_reg[3]) & ~$past(delay_reg[2]))))
    );

endmodule