// SVA for DPR16X4C
// Bind-friendly checker module. Focused, high-signal-coverage, concise.

module dpr16x4c_sva (
    input  logic        WCK,
    input  logic        WRE,
    input  logic [3:0]  DI,
    input  logic [3:0]  RAD,
    input  logic [3:0]  WAD,
    input  logic [3:0]  DO,

    // internal DUT state via bind
    input  logic [3:0]  ram [0:15],
    input  logic [63:0] conv_initval
);
    default clocking cb @ (posedge WCK); endclocking

    // Track if an address has been written since time 0
    logic [15:0] written;
    initial written = '0;
    always_ff @(posedge WCK) if (WRE && !$isunknown(WAD)) written[WAD] <= 1'b1;

    // Basic X/Z sanitization on use
    assert property (!$isunknown(WRE));
    assert property (!$isunknown(RAD));
    assert property (!WRE or (!$isunknown(DI) && !$isunknown(WAD)));
    assert property (WRE  -> (!$isunknown(DI) && !$isunknown(WAD)));

    // Combinational read correctness (4-state equality)
    assert property (DO === ram[RAD]);

    // Unreachable RAD>15 branch is indeed unreachable; if it ever were, DO must be 0
    assert property (!(RAD > 4'd15));
    assert property ((RAD > 4'd15) |-> (DO == 4'h0));

    // Write behavior: written location updates next cycle to DI
    assert property (WRE |=> ram[$past(WAD)] == $past(DI));

    // Per-address invariants and coverage
    genvar a;
    generate for (a = 0; a < 16; a++) begin : A
        // Only the targeted address may change on a write
        assert property ((!WRE || (WAD != a[3:0])) |=> $stable(ram[a]));

        // If we write this address, it takes DI
        assert property ((WRE && (WAD == a[3:0])) |=> ram[a] == $past(DI));

        // Until first write to this address, contents match conv_initval
        assert property (!written[a] |-> (ram[a] === conv_initval[4*a +: 4]));

        // Coverage: observe reads/writes to every address
        cover property (RAD == a[3:0]);
        cover property (WRE && (WAD == a[3:0]));
    end endgenerate

    // Read-during-write scenarios
    cover property (WRE && (WAD == RAD));      // same address
    cover property (WRE && (WAD != RAD));      // different address

    // After a write, next cycle read-same-address returns new data
    assert property (WRE && (WAD == RAD) |=> DO == $past(DI));

    // Write then next-cycle read of same address (coverage)
    cover property (WRE ##1 (RAD == $past(WAD)));

    // Initialization checks at time 0 (after DUT init NBAs)
    initial begin
        #0;
        for (int i = 0; i < 15; i++) assert (ram[i] === conv_initval[4*i +: 4]);
        // Address 15 should also be initialized (will flag the off-by-one bug if not)
        assert (ram[15] === conv_initval[60 +: 4]);
    end
endmodule

// Example bind (place in a separate file or scope where DPR16X4C is visible):
// bind DPR16X4C dpr_chk ( .WCK(WCK), .WRE(WRE), .DI(DI), .RAD(RAD), .WAD(WAD), .DO(DO), .ram(ram), .conv_initval(conv_initval) );
// module dpr_chk import "";  // no package needed
//     dpr16x4c_sva u (.*);
// endmodule