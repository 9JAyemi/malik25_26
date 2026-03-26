module counter_register (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] data, // 8-bit input for the register
    input select,     // Select input to choose between register and counter
    output reg [7:0] sum  // 8-bit output from the system
);

    reg [3:0] counter;  // 4-bit binary counter
    reg [7:0] register; // 8-bit register

    always @(posedge clk) begin
        if (reset) begin
            counter <= 4'b0;
            register <= 8'b0;
            sum <= 8'b0;
        end else begin
            if (select) begin
                register <= data;
                sum <= register + counter;
            end else begin
                counter <= counter + 1;
                sum <= register + counter;
            end
        end
    end

endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] data, // 8-bit input for the register
    input select,     // Select input to choose between register and counter
    output [7:0] sum  // 8-bit output from the system
);

    counter_register cr (
        .clk(clk),
        .reset(reset),
        .data(data),
        .select(select),
        .sum(sum)
    );

endmodule