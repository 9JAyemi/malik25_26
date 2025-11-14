module font_display(
    input [9:0] pix_x,
    input [9:0] pix_y,
    input score_on,
    input logo_on,
    input registration_on,
    input [7:0] font_word,
    output reg [3:0] text_on,
    output reg [6:0] char_addr,
    output reg [3:0] row_addr,
    output reg [2:0] bit_addr,
    output reg [2:0] text_rgb,
    input clk
);

    // FSM states
    parameter IDLE = 2'b00;
    parameter SCORE = 2'b01;
    parameter LOGO = 2'b10;
    parameter REGISTRATION = 2'b11;

    // FSM state and output registers
    reg [1:0] state_reg, state_next;
    reg [6:0] char_addr_reg, char_addr_next;
    reg [3:0] row_addr_reg, row_addr_next;
    reg [2:0] bit_addr_reg, bit_addr_next;
    reg [2:0] text_rgb_reg, text_rgb_next;

    // pixel coordinate registers
    reg [3:0] row_reg, bit_reg;

    // FSM state machine
    always @* begin
        state_next = IDLE;
        char_addr_next = 7'h00;
        row_addr_next = pix_y[5:2];
        bit_addr_next = pix_x[4:2];
        text_rgb_next = 3'b110;
        case(pix_x[8:5])
            4'h5: begin
                state_next = SCORE;
                char_addr_next = 7'h47; // G
                text_rgb_next = 3'b001; // green
            end
            4'h6: begin
                state_next = SCORE;
                char_addr_next = 7'h61; // a
                text_rgb_next = 3'b001; // green
            end
            4'h7: begin
                state_next = SCORE;
                char_addr_next = 7'h6d; // m
                text_rgb_next = 3'b001; // green
            end
            4'h8: begin
                state_next = SCORE;
                char_addr_next = 7'h65; // e
                text_rgb_next = 3'b001; // green
            end
            4'h9: begin
                state_next = LOGO;
                char_addr_next = 7'h00; // blank
                text_rgb_next = 3'b110; // yellow
            end
            4'ha: begin
                state_next = LOGO;
                char_addr_next = 7'h4f; // O
                text_rgb_next = 3'b011; // orange
            end
            4'hb: begin
                state_next = LOGO;
                char_addr_next = 7'h76; // v
                text_rgb_next = 3'b011; // orange
            end
            4'hc: begin
                state_next = LOGO;
                char_addr_next = 7'h65; // e
                text_rgb_next = 3'b011; // orange
            end
            default: begin
                state_next = REGISTRATION;
                char_addr_next = 7'h72; // r
                text_rgb_next = 3'b001; // green
            end
        endcase
    end

    // update state and output registers
    always @(posedge clk) begin
        state_reg <= state_next;
        char_addr_reg <= char_addr_next;
        row_addr_reg <= row_addr_next;
        bit_addr_reg <= bit_addr_next;
        text_rgb_reg <= text_rgb_next;
    end

    // update pixel coordinate registers
    always @(posedge clk) begin
        row_reg <= pix_y[1:0];
        bit_reg <= pix_x[1:0];
    end

    // multiplexer for font ROM addresses and rgb
    always @* begin
        text_on = state_reg;
        case(state_reg)
            IDLE: begin
                char_addr = char_addr_reg;
                row_addr = row_addr_reg;
                bit_addr = bit_addr_reg;
                text_rgb = text_rgb_reg;
            end
            SCORE: begin
                char_addr = char_addr_reg;
                row_addr = row_reg + (char_addr_reg[6:0] << 2);
                bit_addr = bit_reg;
                text_rgb = text_rgb_reg;
            end
            LOGO: begin
                char_addr = char_addr_reg;
                row_addr = row_reg + (char_addr_reg[6:0] << 2);
                bit_addr = bit_reg;
                if (font_word[bit_reg])
                    text_rgb = text_rgb_reg;
                else
                    text_rgb = 3'b110; // yellow
            end
            REGISTRATION: begin
                char_addr = char_addr_reg;
                row_addr = row_addr_reg;
                bit_addr = bit_addr_reg;
                text_rgb = text_rgb_reg;
            end
        endcase
    end

endmodule