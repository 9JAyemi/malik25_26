
module commutation_top(
    input clk,
    input enable_i,
    input reset_i,
    input advance_i,
    input direction_i,
    input break_i,
    input align_i,
    output reg [3:0] state_o
);

parameter STATE_IDLE = 4'b0000;
parameter STATE_ADVANCE = 4'b0001;
parameter STATE_BREAK = 4'b0010;
parameter STATE_ALIGN = 4'b0011;

always @(posedge clk) begin
    if (reset_i) begin
        state_o <= STATE_IDLE;
    end else begin
        case (state_o)
            STATE_IDLE: begin
                if (enable_i) begin
                    if (advance_i) begin
                        state_o <= STATE_ADVANCE;
                    end else if (break_i) begin
                        state_o <= STATE_BREAK;
                    end else if (align_i) begin
                        state_o <= STATE_ALIGN;
                    end else begin
                        state_o <= STATE_IDLE;
                    end
                end else begin
                    state_o <= STATE_IDLE;
                end
            end
            STATE_ADVANCE: begin
                if (direction_i) begin
                    state_o <= STATE_IDLE;
                end else begin
                    state_o <= STATE_ADVANCE;
                end
            end
            STATE_BREAK: begin
                state_o <= STATE_IDLE;
            end
            STATE_ALIGN: begin
                state_o <= STATE_IDLE;
            end
            default: begin
                state_o <= STATE_IDLE;
            end
        endcase
    end
end

endmodule
module timer(
    input clk,
    input enable_i,
    input reset_i,
    input [15:0] compare_i,
    input [15:0] autoreload_i,
    output compare_o,
    output [15:0] value_o
);

reg [15:0] counter;

always @(posedge clk) begin
    if (reset_i) begin
        counter <= 16'b0;
    end else if (enable_i) begin
        if (counter == compare_i) begin
            counter <= autoreload_i;
        end else begin
            counter <= counter + 1'b1;
        end
    end else begin
        counter <= counter;
    end
end

assign compare_o = (counter == compare_i);
assign value_o = counter;

endmodule
module debouncer(
    input clk_i,
    input reset_i,
    input pin_i,
    output pos_o,
    output neg_o,
    output debounced_o
);

parameter DEBOUNCE_COUNT = 2;

reg [DEBOUNCE_COUNT-1:0] counter;
reg prev_pin_i;
reg pos_flag;
reg neg_flag;

always @(posedge clk_i) begin
    if (reset_i) begin
        counter <= {DEBOUNCE_COUNT{1'b0}};
        prev_pin_i <= 1'b0;
        pos_flag <= 1'b0;
        neg_flag <= 1'b0;
    end else begin
        counter <= counter + 1'b1;
        prev_pin_i <= pin_i;
        if (pin_i && !prev_pin_i) begin
            pos_flag <= 1'b1;
        end else begin
            pos_flag <= 1'b0;
        end
        if (!pin_i && prev_pin_i) begin
            neg_flag <= 1'b1;
        end else begin
            neg_flag <= 1'b0;
        end
    end
end

assign pos_o = pos_flag;
assign neg_o = neg_flag;
assign debounced_o = counter == DEBOUNCE_COUNT;

endmodule