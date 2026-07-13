module and_gate_sva (
    input logic A,
    input logic B,
    input logic Z
);
    // Output matches A & B when A rises.
    check_z_on_A_posedge: assert property (
        @(posedge A) Z == (A & B)
    );

    // Output matches A & B when A falls.
    check_z_on_A_negedge: assert property (
        @(negedge A) Z == (A & B)
    );

    // Output matches A & B when B rises.
    check_z_on_B_posedge: assert property (
        @(posedge B) Z == (A & B)
    );

    // Output matches A & B when B falls.
    check_z_on_B_negedge: assert property (
        @(negedge B) Z == (A & B)
    );

    // If Z rises, both inputs must be HIGH.
    check_inputs_on_Z_posedge: assert property (
        @(posedge Z) (A & B)
    );

    // If Z falls, at least one input must be LOW.
    check_inputs_on_Z_negedge: assert property (
        @(negedge Z) !(A & B)
    );
endmodule