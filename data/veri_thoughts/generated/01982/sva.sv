module mult_module_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic enable,
    input logic [15:0] Z
);
    // Z must be zero when enable is LOW.
    check_zero_when_disabled: assert property (
        @(posedge $global_clock) (enable == 1'b0) |-> (Z === 16'b0)
    );

    // Z must equal A*B when enable is HIGH.
    check_product_when_enabled: assert property (
        @(posedge $global_clock) (enable == 1'b1) |-> (Z == (A * B))
    );

    // If enabled and A is zero, Z must be zero.
    check_zero_A_zero: assert property (
        @(posedge $global_clock) (enable && (A == 8'd0)) |-> (Z === 16'b0)
    );

    // If enabled and B is zero, Z must be zero.
    check_zero_B_zero: assert property (
        @(posedge $global_clock) (enable && (B == 8'd0)) |-> (Z === 16'b0)
    );

    // If enabled and A is one, Z equals B (zero-extended to 16 bits).
    check_identity_A_one: assert property (
        @(posedge $global_clock) (enable && (A == 8'd1)) |-> (Z == {8'h00, B})
    );

    // If enabled and B is one, Z equals A (zero-extended to 16 bits).
    check_identity_B_one: assert property (
        @(posedge $global_clock) (enable && (B == 8'd1)) |-> (Z == {8'h00, A})
    );

    // If enabled and A=B=8'hFF, Z must be 16'hFE01 (255*255).
    check_max_corner: assert property (
        @(posedge $global_clock) (enable && (A == 8'hFF) && (B == 8'hFF)) |-> (Z == 16'hFE01)
    );

    // If A, B, and enable are stable, Z must remain stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge $global_clock) $stable({A,B,enable}) |-> $stable(Z)
    );

    // With enable LOW in consecutive cycles, changing A or B must not change Z.
    check_no_output_change_when_disabled_operands_change: assert property (
        @(posedge $global_clock) (enable == 1'b0 && $past(enable,1) == 1'b0 && ($changed(A) || $changed(B))) |-> $stable(Z)
    );

    // When enable rises and A,B are non-zero and stable, Z must change from 0 to product.
    check_enable_rise_updates_Z: assert property (
        @(posedge $global_clock) ($rose(enable) && $stable(A) && $stable(B) && (A != 8'd0) && (B != 8'd0)) |-> $changed(Z)
    );
endmodule