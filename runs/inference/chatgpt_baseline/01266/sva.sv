module AND4_sVA (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);
    // No clock/reset in DUT; pure combinational AND. Sample on posedges of inputs/outputs.

    // Z equals A & B & C & D when A toggles HIGH.
    check_z_eq_and_at_A: assert property (
        @(posedge A) Z == (A & B & C & D)
    );

    // Z equals A & B & C & D when B toggles HIGH.
    check_z_eq_and_at_B: assert property (
        @(posedge B) Z == (A & B & C & D)
    );

    // Z equals A & B & C & D when C toggles HIGH.
    check_z_eq_and_at_C: assert property (
        @(posedge C) Z == (A & B & C & D)
    );

    // Z equals A & B & C & D when D toggles HIGH.
    check_z_eq_and_at_D: assert property (
        @(posedge D) Z == (A & B & C & D)
    );

    // Z equals A & B & C & D when Z toggles HIGH.
    check_z_eq_and_at_Z: assert property (
        @(posedge Z) Z == (A & B & C & D)
    );

    // If Z rises, all inputs must be HIGH.
    check_z_rise_inputs_high: assert property (
        @(posedge Z) (A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)
    );
endmodule