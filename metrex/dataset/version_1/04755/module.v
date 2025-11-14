module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input select,     // Select input to choose between counters and multiplexer
    output reg [3:0] out  // 4-bit output from the active module
);

    reg [3:0] counter1 = 4'b0000;   // 4-bit binary counter from 0 through 5
    reg [3:0] counter2 = 4'b0000;   // 4-bit binary counter from 0 through 15
    reg [1:0] select_counter = 2'b00;  // Selects which counter to output
    reg [3:0] mux_out;              // Output from the 4-to-1 multiplexer

    always @(posedge clk) begin
        if (reset) begin
            counter1 <= 4'b0000;
            counter2 <= 4'b0000;
            select_counter <= 2'b00;
            mux_out <= 4'b0000;
        end else begin
            if (select) begin
                // Multiplexer is selected
                select_counter <= 2'b10;
                case (counter2)
                    4'b0000: mux_out <= 4'b0000;
                    4'b0001: mux_out <= 4'b0001;
                    4'b0010: mux_out <= 4'b0010;
                    4'b0011: mux_out <= 4'b0011;
                    4'b0100: mux_out <= 4'b0100;
                    4'b0101: mux_out <= 4'b0101;
                    4'b0110: mux_out <= 4'b0110;
                    4'b0111: mux_out <= 4'b0111;
                    4'b1000: mux_out <= 4'b1000;
                    4'b1001: mux_out <= 4'b1001;
                    4'b1010: mux_out <= 4'b1010;
                    4'b1011: mux_out <= 4'b1011;
                    4'b1100: mux_out <= 4'b1100;
                    4'b1101: mux_out <= 4'b1101;
                    4'b1110: mux_out <= 4'b1110;
                    4'b1111: mux_out <= 4'b1111;
                endcase
            end else begin
                // Counters are selected
                select_counter <= 2'b01;
                case (counter1)
                    4'b0000: out <= 4'b0000;
                    4'b0001: out <= 4'b0001;
                    4'b0010: out <= 4'b0010;
                    4'b0011: out <= 4'b0011;
                    4'b0100: out <= 4'b0100;
                    4'b0101: out <= 4'b0101;
                    4'b0110: out <= 4'b0110;
                    4'b0111: out <= 4'b0111;
                    4'b1000: out <= 4'b1000;
                    4'b1001: out <= 4'b0001;
                    4'b1010: out <= 4'b0010;
                    4'b1011: out <= 4'b0011;
                    4'b1100: out <= 4'b0100;
                    4'b1101: out <= 4'b0101;
                    4'b1110: out <= 4'b0110;
                    4'b1111: out <= 4'b0111;
                endcase
                if (counter1 == 4'b0101) begin
                    counter1 <= 4'b0000;
                    counter2 <= counter2 + 1;
                end else begin
                    counter1 <= counter1 + 1;
                end
            end
        end
    end
endmodule