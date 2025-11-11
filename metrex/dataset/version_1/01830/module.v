module serial_interface (
    input reset,
    input clk,
    input [3:0] mcu_data,
    input mcu_data_valid,
    input [3:0] periph_data,
    input periph_data_valid,
    output reg mcu_data_ready,
    output reg periph_data_ready,
    output reg [3:0] mcu_response,
    output reg [3:0] periph_response
);

    reg [3:0] mcu_buffer;
    reg [3:0] periph_buffer;
    reg [1:0] state_reg = 2'b00;

    always @(posedge clk) begin
        if (reset) begin
            state_reg <= 2'b00;
            mcu_buffer <= 4'b0;
            periph_buffer <= 4'b0;
            mcu_data_ready <= 1'b0;
            periph_data_ready <= 1'b0;
            mcu_response <= 4'b0;
            periph_response <= 4'b0;
        end
        else begin
            case (state_reg)
                2'b00: // Idle state
                    begin
                        if (mcu_data_valid && !periph_data_ready) begin
                            // Store data in buffer
                            mcu_buffer <= mcu_data;
                            // Set data ready signal
                            mcu_data_ready <= 1'b1;
                            // Move to next state
                            state_reg <= 2'b01;
                        end
                        else if (!mcu_data_ready && periph_data_valid) begin
                            // Store data in buffer
                            periph_buffer <= periph_data;
                            // Set data ready signal
                            periph_data_ready <= 1'b1;
                            // Move to next state
                            state_reg <= 2'b10;
                        end
                    end
                2'b01: // Wait for peripheral device to be ready
                    begin
                        if (periph_data_ready) begin
                            // Transfer data to peripheral device
                            periph_response <= mcu_buffer;
                            // Clear data ready signals
                            mcu_data_ready <= 1'b0;
                            periph_data_ready <= 1'b0;
                            // Move back to idle state
                            state_reg <= 2'b00;
                        end
                    end
                2'b10: // Wait for microcontroller to be ready
                    begin
                        if (mcu_data_ready) begin
                            // Transfer data to microcontroller
                            mcu_response <= periph_buffer;
                            // Clear data ready signals
                            mcu_data_ready <= 1'b0;
                            periph_data_ready <= 1'b0;
                            // Move back to idle state
                            state_reg <= 2'b00;
                        end
                    end
            endcase
        end
    end

endmodule