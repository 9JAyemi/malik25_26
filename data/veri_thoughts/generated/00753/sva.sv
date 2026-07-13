module sparc_exu_aluadder64_sva (
    input logic clk,
    input logic [63:0] rs1_data,
    input logic [63:0] rs2_data,
    input logic cin,
    input logic [63:0] adder_out,
    input logic cout32,
    input logic cout64
);
    // Purely combinational adder; no reset in RTL. Assertions are clocked; no disable condition.

    // Lower 32-bit addition with carry-in produces cout32 and adder_out[31:0].
    check_lower_add_split: assert property (
        @(posedge clk) disable iff (1'b0)
        {cout32, adder_out[31:0]} == ({1'b0, rs1_data[31:0]} + {1'b0, rs2_data[31:0]} + cin)
    );

    // Upper 32-bit addition with cout32 carry-in produces cout64 and adder_out[63:32].
    check_upper_add_split: assert property (
        @(posedge clk) disable iff (1'b0)
        {cout64, adder_out[63:32]} == ({1'b0, rs1_data[63:32]} + {1'b0, rs2_data[63:32]} + cout32)
    );

    // Full 65-bit sum matches concatenated {cout64, adder_out}.
    check_full_65bit_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        {cout64, adder_out} == ({1'b0, rs1_data} + {1'b0, rs2_data} + cin)
    );

    // cout32 equals MSB of the 33-bit lower-half sum.
    check_cout32_is_lower_carry: assert property (
        @(posedge clk) disable iff (1'b0)
        cout32 == (({1'b0, rs1_data[31:0]} + {1'b0, rs2_data[31:0]} + cin)[32])
    );

    // adder_out[31:0] equals lower 32 bits of the lower-half sum.
    check_lo_bits_match: assert property (
        @(posedge clk) disable iff (1'b0)
        adder_out[31:0] == (rs1_data[31:0] + rs2_data[31:0] + cin)
    );

    // cout64 equals MSB of the 33-bit upper-half sum with carry-in cout32.
    check_cout64_is_upper_carry: assert property (
        @(posedge clk) disable iff (1'b0)
        cout64 == (({1'b0, rs1_data[63:32]} + {1'b0, rs2_data[63:32]} + cout32)[32])
    );

    // adder_out[63:32] equals lower 32 bits of the upper-half sum with carry-in cout32.
    check_hi_bits_match: assert property (
        @(posedge clk) disable iff (1'b0)
        adder_out[63:32] == (rs1_data[63:32] + rs2_data[63:32] + cout32)
    );

    // cout64 equals bit[64] of the 65-bit total sum.
    check_cout64_matches_total_carry: assert property (
        @(posedge clk) disable iff (1'b0)
        cout64 == (({1'b0, rs1_data} + {1'b0, rs2_data} + cin)[64])
    );

    // adder_out equals the lower 64 bits of the 65-bit total sum.
    check_adder_out_matches_total_low64: assert property (
        @(posedge clk) disable iff (1'b0)
        adder_out == ({1'b0, rs1_data} + {1'b0, rs2_data} + cin)[63:0]
    );

    // Low outputs depend only on rs1[31:0], rs2[31:0], and cin.
    check_lo_outputs_stable_on_lo_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable(rs1_data[31:0]) && $stable(rs2_data[31:0]) && $stable(cin) |-> $stable({cout32, adder_out[31:0]})
    );

    // High outputs depend only on rs1[63:32], rs2[63:32], and cout32.
    check_hi_outputs_stable_on_hi_inputs_and_cout32_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable(rs1_data[63:32]) && $stable(rs2_data[63:32]) && $stable(cout32) |-> $stable({cout64, adder_out[63:32]})
    );

endmodule