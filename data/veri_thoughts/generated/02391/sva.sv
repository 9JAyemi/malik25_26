module sparc_exu_aluspr_sva (
    input logic [63:0] rs1_data,
    input logic [63:0] rs2_data,
    input logic        cin,
    input logic [63:0] spr_out
);
    // spr_out equals (rs1_data ^ rs2_data) ^ { (rs1_data[62:0] | rs2_data[62:0]), cin }.
    check_result_definition: assert property (
        @($global_clock) spr_out == ((rs1_data ^ rs2_data) ^ { (rs1_data[62:0] | rs2_data[62:0]), cin })
    );

    // High bits do not depend on cin explicitly.
    check_high_bits_independence: assert property (
        @($global_clock) spr_out[63:1] == ((rs1_data[63:1] ^ rs2_data[63:1]) ^ (rs1_data[62:0] | rs2_data[62:0]))
    );

    // Bit 0 equals (rs1_data[0] ^ rs2_data[0]) ^ cin.
    check_bit0_definition: assert property (
        @($global_clock) spr_out[0] == ((rs1_data[0] ^ rs2_data[0]) ^ cin)
    );

    // Bit 1 equals (rs1_data[1] ^ rs2_data[1]) ^ (rs1_data[0] | rs2_data[0]).
    check_bit1_definition: assert property (
        @($global_clock) spr_out[1] == ((rs1_data[1] ^ rs2_data[1]) ^ (rs1_data[0] | rs2_data[0]))
    );

    // Bit 63 equals (rs1_data[63] ^ rs2_data[63]) ^ (rs1_data[62] | rs2_data[62]).
    check_bit63_definition: assert property (
        @($global_clock) spr_out[63] == ((rs1_data[63] ^ rs2_data[63]) ^ (rs1_data[62] | rs2_data[62]))
    );

    // spr_out ^ (rs1_data ^ rs2_data) equals the shifted OR vector.
    check_xor_vs_shiftor: assert property (
        @($global_clock) (spr_out ^ (rs1_data ^ rs2_data)) == { (rs1_data[62:0] | rs2_data[62:0]), cin }
    );

    // Changing cin alone only affects spr_out[0] (upper bits stay stable).
    check_cin_only_affects_bit0_upper_stable: assert property (
        @($global_clock) $changed(cin) && $stable(rs1_data) && $stable(rs2_data) |-> $stable(spr_out[63:1])
    );

    // Changing cin alone causes spr_out[0] to change.
    check_cin_changes_bit0: assert property (
        @($global_clock) $changed(cin) && $stable(rs1_data) && $stable(rs2_data) |-> $changed(spr_out[0])
    );

    // If all inputs are stable, spr_out remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) $stable(rs1_data) && $stable(rs2_data) && $stable(cin) |-> $stable(spr_out)
    );

    // When rs1_data == rs2_data, spr_out equals the shifted OR vector directly.
    check_equal_inputs_reduce_to_shiftor: assert property (
        @($global_clock) (rs1_data == rs2_data) |-> (spr_out == { (rs1_data[62:0] | rs2_data[62:0]), cin })
    );
endmodule