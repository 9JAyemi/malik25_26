module key_expander_sva (
    input logic CLK,
    input logic RESETn,
    input logic [31:0] g_out,
    input logic [127:0] key_in,
    input logic [3:0] round,
    input logic add_w_out,
    input logic enc_dec
);

    localparam integer KEY_WIDTH = 32;
    localparam integer KEY_NUM   = 4;
    localparam integer WORD      = 8;
    localparam integer ROUNDS    = 10;

    wire [KEY_WIDTH - 1 : 0] key [0 : KEY_NUM - 1];
    wire [WORD - 1 : 0] rot_in[0 : KEY_NUM - 1];
    wire [KEY_WIDTH - 1 : 0] g_func;
    reg [WORD - 1 : 0] rc_dir, rc_inv;
    wire [WORD - 1 : 0] rc;

    generate
        genvar i;
        for(i = 0; i < KEY_NUM; i = i + 1)
        begin:KG
            assign key[KEY_NUM - 1 - i] = key_in[KEY_WIDTH*(i + 1) - 1 : KEY_WIDTH*i];
        end
    endgenerate

    generate
        genvar j;
        for(j = 0; j < KEY_NUM; j = j + 1)
        begin:KGO
            if(j == 0)
                assign key_out[KEY_WIDTH*(KEY_NUM - j) - 1 : KEY_WIDTH*(KEY_NUM - j - 1)] = key[j] ^ g_func;
            else
                if(j == 1)
                    assign key_out[KEY_WIDTH*(KEY_NUM - j) - 1 : KEY_WIDTH*(KEY_NUM - j - 1)] = (add_w_out) ? key[j] ^ key[j - 1] ^ g_func : key[j] ^ key[j - 1];
                else
                    assign key_out[KEY_WIDTH*(KEY_NUM - j) - 1 : KEY_WIDTH*(KEY_NUM - j - 1)] = key[j] ^ key[j - 1];
        end
    endgenerate

    generate
        genvar k;
        for(k = 0; k < KEY_NUM; k = k + 1)
        begin:GFIG
            assign rot_in[k] = (enc_dec) ? key[KEY_NUM - 1][WORD*(k + 1) - 1 : WORD*k] : key[KEY_NUM - 1][WORD*(k + 1) - 1 : WORD*k] ^ key[KEY_NUM - 2][WORD*(k + 1) - 1 : WORD*k];
        end
    endgenerate

    generate
        genvar l;
        for(l = 0; l < KEY_NUM; l = l + 1)
        begin:GFIG1
            assign g_in[WORD*(l + 1) - 1 : WORD*l] = rot_in[(KEY_NUM + l - 1)%KEY_NUM];
        end
    endgenerate

    assign g_func = {g_out[KEY_WIDTH - 1 : KEY_WIDTH - WORD] ^ rc, g_out[KEY_WIDTH - WORD - 1 : 0]};

    assign rc = (enc_dec) ? rc_dir : rc_inv;

    always @(*)
    begin: RC_DIR
        integer i;
        for(i = 0; i < ROUNDS; i = i + 1)
            if(round == 8)
                rc_dir = 8'h1b;
            else 
            if(round == 9)
                rc_dir = 8'h36;
            else
                rc_dir = 8'h01 << round;
    end

    always @(*)
    begin: RC_INV
        integer i;
        for(i = 0; i < ROUNDS; i = i + 1)
            if(round == 1)
                rc_inv = 8'h1b;
            else 
            if(round == 0)
                rc_inv = 8'h36;
            else
                rc_inv = 8'h80 >> (round - 2);
    end

    ///// Key expansion logic /////
    // Key expansion must be done for each round.
    key_expansion: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> key_out[127:0] == {key[0], key[1], key[2], key[3]}
    );

    // g_func must be updated based on g_out and rc.
    g_func_update: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> g_func == {g_out[KEY_WIDTH - 1 : KEY_WIDTH - WORD] ^ rc, g_out[KEY_WIDTH - WORD - 1 : 0]}
    );

    // rc must be updated based on enc_dec and round.
    rc_update: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> rc == (enc_dec) ? rc_dir : rc_inv
    );

    // rc_dir must be set correctly for each round.
    rc_dir_set: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> (round == 8) ? (rc_dir == 8'h1b) : (round == 9) ? (rc_dir == 8'h36) : (rc_dir == 8'h01 << round)
    );

    // rc_inv must be set correctly for each round.
    rc_inv_set: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> (round == 1) ? (rc_inv == 8'h1b) : (round == 0) ? (rc_inv == 8'h36) : (rc_inv == 8'h80 >> (round - 2))
    );

    // rot_in must be calculated correctly based on key.
    rot_in_calc: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> rot_in[0] == (enc_dec) ? key[KEY_NUM - 1][WORD*(1 + 1) - 1 : WORD*1] : key[KEY_NUM - 1][WORD*(1 + 1) - 1 : WORD*1] ^ key[KEY_NUM - 2][WORD*(1 + 1) - 1 : WORD*1]
    );

    // g_in must be calculated correctly based on rot_in.
    g_in_calc: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> g_in[WORD*(1 + 1) - 1 : WORD*1] == rot_in[(KEY_NUM + 1 - 1)%KEY_NUM]
    );

    // key_out must be updated correctly based on key and g_func.
    key_out_update: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> key_out[KEY_WIDTH*(KEY_NUM - 1) - 1 : KEY_WIDTH*(KEY_NUM - 2)] == key[1] ^ g_func
    );

    // key_out must be updated correctly based on key and key[1].
    key_out_update_2: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> key_out[KEY_WIDTH*(KEY_NUM - 2) - 1 : KEY_WIDTH*(KEY_NUM - 3)] == key[2] ^ key[1]
    );

    // key_out must be updated correctly based on key and key[2].
    key_out_update_3: assert property (
        @(posedge CLK) disable iff (!RESETn) round inside {[0:ROUNDS]} |-> key_out[KEY_WIDTH*(KEY_NUM - 3) - 1 : KEY_WIDTH*(KEY_NUM - 4)] == key[3] ^ key[2]
    );

endmodule