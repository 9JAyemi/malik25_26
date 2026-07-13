module CRC_serial_m_lfs_XOR_sva
#(
    parameter HASH_LENGTH = 64
)
(
    input logic                    i_message,
    input logic [HASH_LENGTH-1:0]  i_cur_parity,
    input logic [HASH_LENGTH-1:0]  o_next_parity
);

    localparam [0:64] HASH_VALUE = 65'b11001001011011000101011110010101110101111000011100001111010000101;

    // Bit 0 is always the feedback term.
    check_feedback_bit0: assert property (
        @($global_clock)
        o_next_parity[0] == (i_message ^ i_cur_parity[HASH_LENGTH-1])
    );

    genvar i;
    generate
        for (i = 1; i < HASH_LENGTH; i = i + 1) begin : gen_next_parity_checks
            if (HASH_VALUE[i] == 1'b1) begin : gen_tapped_check
                // Tapped bits XOR the shifted parity bit with the feedback term.
                check_tapped_bit: assert property (
                    @($global_clock)
                    o_next_parity[i] == (i_cur_parity[i-1] ^ (i_message ^ i_cur_parity[HASH_LENGTH-1]))
                );
            end
            else begin : gen_shift_check
                // Untapped bits are a pure one-bit shift of the current parity.
                check_shift_bit: assert property (
                    @($global_clock)
                    o_next_parity[i] == i_cur_parity[i-1]
                );
            end
        end
    endgenerate

endmodule