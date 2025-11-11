module ps2_keyboard (
    input CLK,
    input RESET_N,
    input PS2_CLK,
    input PS2_DATA,
    output RX_PRESSED,
    output RX_EXTENDED,
    output [7:0] RX_SCAN
);

reg [7:0] scan_code;
reg rx_pressed;
reg rx_extended;
reg [2:0] bit_count;
reg [3:0] state;
reg [7:0] timer;
reg [7:0] rx_scan;

assign RX_PRESSED = rx_pressed;
assign RX_EXTENDED = rx_extended;
assign RX_SCAN = rx_scan;

parameter IDLE = 3'b000;
parameter START_BIT = 3'b001;
parameter DATA_BIT = 3'b010;
parameter PARITY_BIT = 3'b011;
parameter STOP_BIT = 3'b100;
parameter EXTENDED_CODE = 8'hE0;
parameter RELEASE_CODE = 8'hF0;

always @(posedge CLK or negedge RESET_N) begin
    if (~RESET_N) begin
        scan_code <= 0;
        rx_scan <= 0;
        rx_pressed <= 0;
        rx_extended <= 0;
        bit_count <= 0;
        state <= IDLE;
        timer <= 0;
    end
    else begin
        case (state)
            IDLE: begin
                if (!PS2_CLK && PS2_DATA) begin
                    state <= START_BIT;
                    bit_count <= 0;
                    scan_code <= 0;
                    timer <= 0;
                end
            end
            START_BIT: begin
                if (PS2_CLK) begin
                    state <= DATA_BIT;
                end
            end
            DATA_BIT: begin
                if (!PS2_CLK) begin
                    scan_code[bit_count] <= PS2_DATA;
                    bit_count <= bit_count + 1;
                    if (bit_count == 7) begin
                        state <= PARITY_BIT;
                    end
                end
            end
            PARITY_BIT: begin
                if (PS2_CLK) begin
                    state <= STOP_BIT;
                end
                else begin
                    if (PS2_DATA == ~(scan_code[0]^scan_code[1]^scan_code[2]^scan_code[3]^scan_code[4]^scan_code[5]^scan_code[6])) begin
                        if (scan_code == EXTENDED_CODE) begin
                            rx_extended <= 1;
                            state <= IDLE;
                        end
                        else if (scan_code == RELEASE_CODE) begin
                            rx_pressed <= 0;
                            state <= IDLE;
                        end
                        else begin
                            rx_scan <= scan_code;
                            rx_pressed <= 1;
                            state <= STOP_BIT;
                        end
                    end
                    else begin
                        state <= IDLE;
                    end
                end
            end
            STOP_BIT: begin
                if (PS2_CLK) begin
                    state <= IDLE;
                end
            end
        endcase
        if (!PS2_CLK && !PS2_DATA) begin
            timer <= 0;
        end
        else if (!PS2_CLK && PS2_DATA) begin
            timer <= timer + 1;
            if (timer == 255) begin
                state <= IDLE;
            end
        end
    end
end

endmodule