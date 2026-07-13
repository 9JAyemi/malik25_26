module sky130_fd_sc_ls__einvp_sva (
    input logic Z,
    input logic A,
    input logic TE
);
    // On any input edge, when TE==1 drive Z as ~A.
    check_inv_on_input_edges: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE) (TE === 1'b1) |-> (Z === ~A)
    );

    // On any input edge, when TE==0 tri-state Z.
    check_z_on_input_edges: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE) (TE === 1'b0) |-> (Z === 1'bz)
    );

    // When TE rises, Z must drive ~A immediately.
    check_te_rise_drives_inv: assert property (
        @(posedge TE) (Z === ~A)
    );

    // When TE falls, Z must go high-impedance.
    check_te_fall_tristate: assert property (
        @(negedge TE) (Z === 1'bz)
    );

    // When A rises with TE==1, Z updates to ~A.
    check_a_rise_updates_z_when_enabled: assert property (
        @(posedge A) (TE === 1'b1) |-> (Z === ~A)
    );

    // When A falls with TE==1, Z updates to ~A.
    check_a_fall_updates_z_when_enabled: assert property (
        @(negedge A) (TE === 1'b1) |-> (Z === ~A)
    );

    // Z can transition between 0/1 only when enabled.
    check_z_edges_only_when_enabled: assert property (
        @(posedge Z or negedge Z) (TE === 1'b1)
    );

    // With TE==1 and A known 0/1, Z must be known 0/1 (not X/Z).
    check_no_xz_when_enabled_and_a_known: assert property (
        @(posedge A or negedge A or posedge TE) ((TE === 1'b1) && (A === 1'b0 || A === 1'b1)) |-> (Z === 1'b0 || Z === 1'b1)
    );

    // With TE==0, Z must not be driven to 0/1.
    check_no_drive_when_disabled: assert property (
        @(posedge A or negedge A or negedge TE) (TE === 1'b0) |-> (Z !== 1'b0 && Z !== 1'b1)
    );

    // If TE is 1 and A is stable across an input edge, Z remains stable.
    check_stability_when_inputs_unchanged_enabled: assert property (
        @(posedge A or negedge A or posedge TE or negedge TE)
            ((TE === 1'b1) && ($past(TE) === 1'b1) && ($past(A) === A)) |-> ($past(Z) === Z)
    );
endmodule