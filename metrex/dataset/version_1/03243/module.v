module divider(
    input wire clk,
    input wire rst,
    input wire signed_div_i,
    input wire [31:0] opdata1_i,
    input wire [31:0] opdata2_i,
    input wire start_i,
    input wire annul_i,
    output reg [63:0] result_o,
    output reg ready_o
);

    reg [63:0] quotient;
    reg [31:0] dividend;
    reg [31:0] divisor;
    reg [5:0] counter;
    reg [1:0] state;
    
    always @(posedge clk) begin
        if (rst == 1) begin
            state <= 0;
            ready_o <= 0;
            result_o <= 0;
        end else begin
            case (state)
                0: begin // Idle state
                    if (start_i) begin
                        if (opdata2_i == 0) begin
                            state <= 3; // Division by zero
                        end else begin
                            state <= 1; // Start division
                            counter <= 0;
                            dividend <= opdata1_i;
                            divisor <= opdata2_i;
                            quotient <= 0;
                        end
                    end
                end
                1: begin // Division state
                    if (annul_i) begin
                        state <= 0; // Stop division
                    end else if (counter == 32) begin
                        state <= 2; // End division
                    end else begin
                        if (dividend[31]) begin
                            dividend <= {dividend[30:0], 1'b0};
                            quotient <= {quotient[62:0], 1'b1};
                        end else begin
                            dividend <= {dividend[30:0], 1'b0};
                            quotient <= quotient << 1;
                        end
                        counter <= counter + 1;
                    end
                end
                2: begin // End division state
                    if (signed_div_i && opdata1_i[31] != opdata2_i[31]) begin
                        quotient <= ~quotient + 1; // Fix sign of quotient
                    end
                    result_o <= quotient;
                    ready_o <= 1;
                    state <= 0; // Return to idle state
                end
                3: begin // Division by zero state
                    result_o <= 0;
                    ready_o <= 1;
                    state <= 0; // Return to idle state
                end
            endcase
        end
    end
endmodule