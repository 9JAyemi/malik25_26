module decoder_sva (
    input logic CLK,
    input logic RESETn,
    input logic [2:0] ABC,
    input logic EN,
    input logic [7:0] Y
);
    ///// Functional mapping /////
    // For {ABC,EN}=4'b0001, Y must be 8'b00000001.
    map_0001: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b000) && (EN == 1'b1)) |-> (Y == 8'b00000001)
    );
    // For {ABC,EN}=4'b0010, Y must be 8'b00000010.
    map_0010: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b001) && (EN == 1'b0)) |-> (Y == 8'b00000010)
    );
    // For {ABC,EN}=4'b0011, Y must be 8'b00000100.
    map_0011: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b001) && (EN == 1'b1)) |-> (Y == 8'b00000100)
    );
    // For {ABC,EN}=4'b0100, Y must be 8'b00001000.
    map_0100: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b010) && (EN == 1'b0)) |-> (Y == 8'b00001000)
    );
    // For {ABC,EN}=4'b0101, Y must be 8'b00010000.
    map_0101: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b010) && (EN == 1'b1)) |-> (Y == 8'b00010000)
    );
    // For {ABC,EN}=4'b0110, Y must be 8'b00100000.
    map_0110: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b011) && (EN == 1'b0)) |-> (Y == 8'b00100000)
    );
    // For {ABC,EN}=4'b0111, Y must be 8'b01000000.
    map_0111: assert property (
        @(posedge CLK) disable iff (!RESETn) ((ABC == 3'b011) && (EN == 1'b1)) |-> (Y == 8'b01000000)
    );
    // For all other {ABC,EN} combinations, Y must be 8'b00000000.
    map_default_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        !(((ABC == 3'b000) && (EN == 1'b1)) ||
          ((ABC == 3'b001) && (EN == 1'b0)) ||
          ((ABC == 3'b001) && (EN == 1'b1)) ||
          ((ABC == 3'b010) && (EN == 1'b0)) ||
          ((ABC == 3'b010) && (EN == 1'b1)) ||
          ((ABC == 3'b011) && (EN == 1'b0)) ||
          ((ABC == 3'b011) && (EN == 1'b1))) |-> (Y == 8'b00000000)
    );

    ///// Output shape invariants /////
    // Y is zero or one-hot (at most one bit set).
    check_onehot0: assert property (
        @(posedge CLK) disable iff (!RESETn) $onehot0(Y)
    );
    // Bit 7 of Y is never asserted.
    check_y7_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y[7] == 1'b0)
    );

    ///// Combinational consistency /////
    // If ABC and EN are stable, Y must remain stable.
    stable_inputs_hold_output: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(ABC) && $stable(EN)) |-> $stable(Y)
    );
    // If Y changes, at least one of ABC or EN must have changed.
    output_change_needs_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> $changed({ABC, EN})
    );
endmodule