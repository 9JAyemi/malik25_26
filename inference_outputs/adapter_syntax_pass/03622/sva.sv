module key_expander_sva
(
    input logic [127:0] key_out,
    input logic [31:0]  g_in,
    input logic [31:0]  g_out,
    input logic [127:0] key_in,
    input logic [3:0]   round,
    input logic         add_w_out,
    input logic         enc_dec
);

    localparam integer KEY_WIDTH = 32;
    localparam integer KEY_NUM   = 4;
    localparam integer WORD      = 8;
    localparam integer ROUNDS    = 10;

    wire [KEY_WIDTH-1:0] key [0:KEY_NUM-1];
    wire [WORD-1:0]      rot_in [0:KEY_NUM-1];
    wire [KEY_WIDTH-1:0] g_func;
    wire [WORD-1:0]      rc_dir, rc_inv;
    wire [WORD-1:0]      rc;

    generate
        genvar i;
        for (i = 0; i < KEY_NUM; i = i + 1) begin : KG
            assign key[KEY_NUM-1-i] = key_in[KEY_WIDTH*(i+1)-1:KEY_WIDTH*i];
        end
    endgenerate

    generate
        genvar j;
        for (j = 0; j < KEY_NUM; j = j + 1) begin : KGO
            if (j == 0) begin : KGO0
                assign key_out[KEY_WIDTH*(KEY_NUM-j)-1:KEY_WIDTH*(KEY_NUM-j-1)] = key[j] ^ g_func;
            end else if (j == 1) begin : KGO1
                assign key_out[KEY_WIDTH*(KEY_NUM-j)-1:KEY_WIDTH*(KEY_NUM-j-1)] = (add_w_out) ? key[j] ^ key[j-1] ^ g_func : key[j] ^ key[j-1];
            end else begin : KGO2
                assign key_out[KEY_WIDTH*(KEY_NUM-j)-1:KEY_WIDTH*(KEY_NUM-j-1)] = key[j] ^ key[j-1];
            end
        end
    endgenerate

    generate
        genvar k;
        for (k = 0; k < KEY_NUM; k = k + 1) begin : GFIG
            assign rot_in[k] = (enc_dec) ? key[KEY_NUM-1][WORD*(k+1)-1:WORD*k] : key[KEY_NUM-1][WORD*(k+1)-1:WORD*k] ^ key[KEY_NUM-2][WORD*(k+1)-1:WORD*k];
        end
    endgenerate

    generate
        genvar l;
        for (l = 0; l < KEY_NUM; l = l + 1) begin : GFIG1
            assign g_in[WORD*(l+1)-1:WORD*l] = rot_in[(KEY_NUM+l-1)%KEY_NUM];
        end
    endgenerate

    assign g_func = {g_out[KEY_WIDTH-1:KEY_WIDTH-WORD] ^ rc, g_out[KEY_WIDTH-WORD-1:0]};

    assign rc = (enc_dec) ? rc_dir : rc_inv;

    // rc_dir is 0x01 shifted by the current round.
    check_rc_dir_shift: assert property (
        @($global_clock)
        rc_dir == (8'h01 << round)
    );

    // rc_inv is 0x80 shifted right by (round - 2) for rounds 2 through 10.
    check_rc_inv_shift: assert property (
        @($global_clock)
        (round inside {[2:10]}) |-> (rc_inv == (8'h80 >> (round - 2)))
    );

    // rc_inv is 0x1b when round is 1.
    check_rc_inv_round1: assert property (
        @($global_clock)
        (round == 1) |-> (rc_inv == 8'h1b)
    );

    // rc_inv is 0x36 when round is 0.
    check_rc_inv_round0: assert property (
        @($global_clock)
        (round == 0) |-> (rc_inv == 8'h36)
    );

    // rc_dir is 0x1b when round is 8.
    check_rc_dir_round8: assert property (
        @($global_clock)
        (round == 8) |-> (rc_dir == 8'h1b)
    );

    // rc_dir is 0x36 when round is 9.
    check_rc_dir_round9: assert property (
        @($global_clock)
        (round == 9) |-> (rc_dir == 8'h36)
    );

    // rc_dir is 0x01 when round is 10.
    check_rc_dir_round10: assert property (
        @($global_clock)
        (round == 10) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 0.
    check_rc_dir_round0: assert property (
        @($global_clock)
        (round == 0) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 1.
    check_rc_dir_round1: assert property (
        @($global_clock)
        (round == 1) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 2.
    check_rc_dir_round2: assert property (
        @($global_clock)
        (round == 2) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x02 when round is 3.
    check_rc_dir_round3: assert property (
        @($global_clock)
        (round == 3) |-> (rc_dir == 8'h02)
    );

    // rc_dir is 0x04 when round is 4.
    check_rc_dir_round4: assert property (
        @($global_clock)
        (round == 4) |-> (rc_dir == 8'h04)
    );

    // rc_dir is 0x08 when round is 5.
    check_rc_dir_round5: assert property (
        @($global_clock)
        (round == 5) |-> (rc_dir == 8'h08)
    );

    // rc_dir is 0x10 when round is 6.
    check_rc_dir_round6: assert property (
        @($global_clock)
        (round == 6) |-> (rc_dir == 8'h10)
    );

    // rc_dir is 0x20 when round is 7.
    check_rc_dir_round7: assert property (
        @($global_clock)
        (round == 7) |-> (rc_dir == 8'h20)
    );

    // rc_dir is 0x40 when round is 8.
    check_rc_dir_round8: assert property (
        @($global_clock)
        (round == 8) |-> (rc_dir == 8'h40)
    );

    // rc_dir is 0x80 when round is 9.
    check_rc_dir_round9: assert property (
        @($global_clock)
        (round == 9) |-> (rc_dir == 8'h80)
    );

    // rc_dir is 0x01 when round is 10.
    check_rc_dir_round10: assert property (
        @($global_clock)
        (round == 10) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 11.
    check_rc_dir_round11: assert property (
        @($global_clock)
        (round == 11) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 12.
    check_rc_dir_round12: assert property (
        @($global_clock)
        (round == 12) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 13.
    check_rc_dir_round13: assert property (
        @($global_clock)
        (round == 13) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 14.
    check_rc_dir_round14: assert property (
        @($global_clock)
        (round == 14) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 15.
    check_rc_dir_round15: assert property (
        @($global_clock)
        (round == 15) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 16.
    check_rc_dir_round16: assert property (
        @($global_clock)
        (round == 16) |-> (rc_dir == 8'h01)
    );

    // rc_dir is 0x01 when round is 17.
    check_rc_dir_round17: assert property (
        @($global_clock)
        (