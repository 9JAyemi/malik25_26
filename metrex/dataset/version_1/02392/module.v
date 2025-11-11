
module top_module (
    input clk,
    input reset,          // Synchronous active-high reset
    input [9:0] d,        // 10-bit input for the shift register
    output [9:0] q,       // 10-bit output from the active module
    output [9:0] count_out // 10-bit output from the binary counter
);

    // Shift register using ring counter architecture
    reg [9:0] shift_reg [0:9];
    reg [3:0] shift_sel = 4'b0001;
    always @(posedge clk) begin
        if (reset) begin
            shift_sel <= 4'b0001;
        end
        else begin
            shift_reg[shift_sel] <= d;
            shift_sel <= (shift_sel == 4'b1000) ? 4'b0001 : (shift_sel + 1);
        end
    end
    assign q = shift_reg[shift_sel];

    // Binary counter
    reg [9:0] binary_counter = 10'b0;
    always @(posedge clk) begin
        if (reset) begin
            binary_counter <= 10'b0;
        end
        else begin
            binary_counter <= (binary_counter == 10'b1111111111) ? 10'b0 : binary_counter + 1;
        end
    end
    assign count_out = binary_counter;

    // Functional unit
    reg [19:0] mult_out = 20'b0;
    reg select = 1'b0;
    always @(posedge clk) begin
        if(reset) begin
            mult_out <= 20'b0;
            select <= 1'b0;
        end
        else begin
            if(select)begin
                mult_out <= shift_reg[shift_sel] * count_out;
            end
            else begin
                mult_out <= count_out * shift_reg[shift_sel];
            end
        end
    end

    // Control logic
    always @(posedge clk) begin
        if(reset) begin
            select <= 1'b0;
        end
        else begin
            select <= (binary_counter == 10'b1111111111) ? 1'b1 : select;
        end
    end

endmodule