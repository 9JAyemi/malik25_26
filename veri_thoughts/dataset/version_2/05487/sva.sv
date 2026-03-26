module IRDA_RECEIVE_Terasic_sva (
    input logic        iCLK,
    input logic        iRST_n,
    input logic        iIRDA,
    input logic        iREAD,
    input logic        oDATA_REAY,
    input logic [31:0] oDATA,
    input logic        DATA_REAY,
    input logic [17:0] idle_count,
    input logic        idle_count_flag,
    input logic [17:0] state_count,
    input logic        state_count_flag,
    input logic [17:0] data_count,
    input logic        data_count_flag,
    input logic [5:0]  bitcount,
    input logic [1:0]  state,
    input logic [31:0] DATA,
    input logic [31:0] DATA_BUF
);

    localparam logic [1:0] IDLE      = 2'b00;
    localparam logic [1:0] GUIDANCE  = 2'b01;
    localparam logic [1:0] DATAREAD  = 2'b10;

    localparam logic [17:0] IDLE_HIGH_DUR     = 18'd262143;
    localparam logic [17:0] GUIDE_LOW_DUR     = 18'd230000;
    localparam logic [17:0] GUIDE_HIGH_DUR    = 18'd210000;
    localparam logic [17:0] DATA_HIGH_DUR     = 18'd41500;
    localparam logic [17:0] BIT_AVAILABLE_DUR = 18'd20000;

    // Reset returns the registered control state and counters to their cleared values.
    reset_values_check: assert property (
        @(posedge iCLK)
        !iRST_n |=> ((idle_count == 18'd0) &&
                     (idle_count_flag == 1'b0) &&
                     (state_count == 18'd0) &&
                     (state_count_flag == 1'b0) &&
                     (data_count == 18'd0) &&
                     (data_count_flag == 1'b0) &&
                     (bitcount == 6'd0) &&
                     (state == IDLE) &&
                     (DATA == 32'd0) &&
                     (DATA_REAY == 1'b0) &&
                     (oDATA == 32'd0))
    );

    // The output ready port mirrors the internal ready register.
    ready_output_mirror_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        (oDATA_REAY == DATA_REAY)
    );

    // idle_count_flag is asserted after an IDLE cycle with iIRDA low.
    idle_flag_set_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == IDLE) && !iIRDA) |=> idle_count_flag
    );

    // idle_count_flag is cleared after any cycle that is not IDLE with iIRDA low.
    idle_flag_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !((state == IDLE) && !iIRDA) |=> !idle_count_flag
    );

    // idle_count increments when its enable flag is high.
    idle_count_increment_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        idle_count_flag |=> (idle_count == ($past(idle_count) + 18'd1))
    );

    // idle_count clears when its enable flag is low.
    idle_count_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !idle_count_flag |=> (idle_count == 18'd0)
    );

    // state_count_flag is asserted after a GUIDANCE cycle with iIRDA high.
    guidance_flag_set_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == GUIDANCE) && iIRDA) |=> state_count_flag
    );

    // state_count_flag is cleared outside GUIDANCE with iIRDA high.
    guidance_flag_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !((state == GUIDANCE) && iIRDA) |=> !state_count_flag
    );

    // state_count increments when its enable flag is high.
    state_count_increment_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        state_count_flag |=> (state_count == ($past(state_count) + 18'd1))
    );

    // state_count clears when its enable flag is low.
    state_count_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !state_count_flag |=> (state_count == 18'd0)
    );

    // IDLE moves to GUIDANCE once the low duration threshold is exceeded.
    idle_to_guidance_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == IDLE) && (idle_count > GUIDE_LOW_DUR)) |=> (state == GUIDANCE)
    );

    // IDLE remains IDLE while the low duration threshold is not exceeded.
    idle_hold_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == IDLE) && (idle_count <= GUIDE_LOW_DUR)) |=> (state == IDLE)
    );

    // GUIDANCE moves to DATAREAD once the high duration threshold is exceeded.
    guidance_to_dataread_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == GUIDANCE) && (state_count > GUIDE_HIGH_DUR)) |=> (state == DATAREAD)
    );

    // GUIDANCE holds until the high duration threshold is exceeded.
    guidance_hold_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == GUIDANCE) && (state_count <= GUIDE_HIGH_DUR)) |=> (state == GUIDANCE)
    );

    // DATAREAD returns to IDLE on long inactivity or after bitcount reaches 33 or more.
    dataread_to_idle_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == DATAREAD) && ((data_count >= IDLE_HIGH_DUR) || (bitcount >= 6'd33))) |=> (state == IDLE)
    );

    // DATAREAD holds while neither exit condition is met.
    dataread_hold_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == DATAREAD) && (data_count < IDLE_HIGH_DUR) && (bitcount < 6'd33)) |=> (state == DATAREAD)
    );

    // Any illegal state encoding returns to IDLE.
    illegal_state_return_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        (state == 2'b11) |=> (state == IDLE)
    );

    // data_count_flag is asserted after a DATAREAD cycle with iIRDA high.
    data_flag_set_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == DATAREAD) && iIRDA) |=> data_count_flag
    );

    // data_count_flag is cleared outside DATAREAD with iIRDA high.
    data_flag_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !((state == DATAREAD) && iIRDA) |=> !data_count_flag
    );

    // data_count increments when its enable flag is high.
    data_count_increment_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        data_count_flag |=> (data_count == ($past(data_count) + 18'd1))
    );

    // data_count clears when its enable flag is low.
    data_count_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !data_count_flag |=> (data_count == 18'd0)
    );

    // bitcount resets whenever the current state is not DATAREAD.
    bitcount_reset_outside_dataread_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        (state != DATAREAD) |=> (bitcount == 6'd0)
    );

    // bitcount increments when data_count hits the bit-available duration in DATAREAD.
    bitcount_increment_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == DATAREAD) && (data_count == BIT_AVAILABLE_DUR)) |=> (bitcount == ($past(bitcount) + 6'd1))
    );

    // bitcount holds in DATAREAD when the bit-available duration is not hit.
    bitcount_hold_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((state == DATAREAD) && (data_count != BIT_AVAILABLE_DUR)) |=> (bitcount == $past(bitcount))
    );

    // DATA clears whenever the current state is not DATAREAD.
    data_clear_outside_dataread_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        (state != DATAREAD) |=> (DATA == 32'd0)
    );

    // A valid complemented header at bitcount 32 captures DATA into DATA_BUF and raises ready.
    ready_set_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        ((bitcount == 6'd32) && (DATA[31:24] == (~DATA[23:16]))) |=> (DATA_REAY && (DATA_BUF == $past(DATA)))
    );

    // Ready clears whenever the valid complemented header condition is not met.
    ready_clear_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !((bitcount == 6'd32) && (DATA[31:24] == (~DATA[23:16]))) |=> !DATA_REAY
    );

    // oDATA loads DATA_BUF when read is requested while ready is high.
    odata_load_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        (iREAD && DATA_REAY) |=> (oDATA == $past(DATA_BUF))
    );

    // oDATA holds its previous value when no read-ready handshake occurs.
    odata_hold_check: assert property (
        @(posedge iCLK) disable iff (!iRST_n)
        !(iREAD && DATA_REAY) |=> (oDATA == $past(oDATA))
    );

endmodule