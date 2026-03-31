```systemverilog
module mdc_mdio_sva (
    input logic mdio_mdc,
    input logic mdio_in_w,
    input logic mdio_in_r,
    output logic [1:0] speed_select,
    output logic duplex_mode
);
    localparam IDLE     = 2'b01;
    localparam ACQUIRE  = 2'b10;

    reg [1:0] current_state;
    reg [1:0] next_state;
    reg [31:0] data_in;
    reg [31:0] data_in_r;
    reg [5:0] data_counter;
    reg [1:0] speed_select_reg;
    reg duplex_mode_reg;

    assign current_state = current_state;
    assign next_state = next_state;
    assign data_in = data_in;
    assign data_in_r = data_in_r;
    assign data_counter = data_counter;
    assign speed_select_reg = speed_select_reg;
    assign duplex_mode_reg = duplex_mode_reg;

    always @(posedge mdio_mdc) begin
        current_state <= next_state;
        data_in <= {data_in[30:0], mdio_in_w};
        if (current_state == ACQUIRE) begin
            data_counter <= data_counter + 1;
        end else begin
            data_counter <= 0;
        end
        if (data_counter == 6'h1f) begin
            if (data_in[31] == 1'b0 && data_in[29:28] == 2'b10 && data_in[27:23] == 5'b10000 && data_in[22:18] == 5'h11) begin
                speed_select_reg <= data_in_r[16:15];
                duplex_mode_reg <= data_in_r[14];
            end
        end
    end

    always @(negedge mdio_mdc) begin
        data_in_r <= {data_in_r[30:0], mdio_in_r};
    end

    always @(*) begin
        case (current_state)
            IDLE: begin
                if (preamble == 1 && mdio_in_w == 0) begin
                    next_state <= ACQUIRE;
                end else begin
                    next_state <= IDLE;
                end
            end
            ACQUIRE: begin
                if (data_counter == 6'h1f) begin
                    next_state <= IDLE;
                end else begin
                    next_state <= ACQUIRE;
                end
            end
            default: begin
                next_state <= IDLE;
            end
        endcase
    end

    // Check that speed_select and duplex_mode are updated correctly
    update_speed_select: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (data_counter == 6'h1f) |-> (speed_select == speed_select_reg)
    );
    update_duplex_mode: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (data_counter == 6'h1f) |-> (duplex_mode == duplex_mode_reg)
    );

    // Check that speed_select and duplex_mode are not updated when not in ACQUIRE state
    no_update_speed_select: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (current_state != ACQUIRE) |-> (speed_select == speed_select_reg)
    );
    no_update_duplex_mode: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (current_state != ACQUIRE) |-> (duplex_mode == duplex_mode_reg)
    );

    // Check that data_in_r is updated on the falling edge of mdio_mdc
    data_in_r_update: assert property (
        @(negedge mdio_mdc) disable iff (!mdio_mdc) (data_in_r[31] == 1'b0 && data_in_r[29:28] == 2'b10 && data_in_r[27:23] == 5'b10000 && data_in_r[22:18] == 5'h11) |-> (speed_select == data_in_r[16:15] && duplex_mode == data_in_r[14])
    );

    // Check that data_in is updated on the rising edge of mdio_mdc
    data_in_update: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (data_in[31] == 1'b0 && data_in[29:28] == 2'b10 && data_in[27:23] == 5'b10000 && data_in[22:18] == 5'h11) |-> (speed_select == data_in[16:15] && duplex_mode == data_in[14])
    );

    // Check that current_state transitions correctly from IDLE to ACQUIRE
    state_transition_idle_to_acquire: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (preamble == 1 && mdio_in_w == 0) |-> (current_state == ACQUIRE)
    );

    // Check that current_state transitions correctly from ACQUIRE to IDLE
    state_transition_acquire_to_idle: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (data_counter == 6'h1f) |-> (current_state == IDLE)
    );

    // Check that next_state is updated correctly in IDLE state
    next_state_update_idle: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (current_state == IDLE) |-> (next_state == (preamble == 1 && mdio_in_w == 0 ? ACQUIRE : IDLE))
    );

    // Check that next_state is updated correctly in ACQUIRE state
    next_state_update_acquire: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (current_state == ACQUIRE) |-> (next_state == (data_counter == 6'h1f ? IDLE : ACQUIRE))
    );

    // Check that data_counter is incremented correctly in ACQUIRE state
    data_counter_increment: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (current_state == ACQUIRE) |-> (data_counter == 6'h1f ? data_counter == 6'h1f : data_counter == data_counter + 1)
    );

    // Check that data_counter is reset to 0 in IDLE state
    data_counter_reset: assert property (
        @(posedge mdio_mdc) disable iff (!mdio_mdc) (current_state == IDLE) |-> (data_counter == 0)
    );
endmodule
```