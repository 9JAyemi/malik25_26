module shift_register_counter (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // 8-bit input for the register
    input select,     // Select input to choose between register and counter
    output [7:0] q    // 8-bit output from the AND module
);

    reg [7:0] shift_reg;
    reg [3:0] counter;
    
    always @(posedge clk) begin
        if (reset) begin
            shift_reg <= 8'h5A;
            counter <= 4'h0;
        end else begin
            if (select) begin
                shift_reg <= {shift_reg[6:0], d[0]};
            end else begin
                counter <= counter + 1;
            end
        end
    end
    
    assign q = shift_reg & {4'hF, counter};
    
endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // 8-bit input for the register
    input select,     // Select input to choose between register and counter
    output [7:0] q    // 8-bit output from the AND module
);

    shift_register_counter src (
        .clk(clk),
        .reset(reset),
        .d(d),
        .select(select),
        .q(q)
    );
    
endmodule