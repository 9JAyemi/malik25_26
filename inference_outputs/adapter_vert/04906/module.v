
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] signed_mag, // 4-bit input for the signed magnitude converter
    input select,     // Select input to choose between counter and converter
    output [7:0] q    // 8-bit output from the functional module
);

    // Instantiate the binary counter module
    binary_counter counter (
        .clk(clk),
        .reset(reset),
        .count(counter_out)
    );

    // Instantiate the signed magnitude to 2's complement converter module
    signed_mag_to_twos_comp converter (
        .signed_mag(signed_mag),
        .twos_comp(converter_out)
    );

    // Define the output signals from the two modules
    reg [3:0] counter_out;
    reg [3:0] converter_out;

    // Define the output signal from the functional module
    reg [7:0] functional_out;

    // Define the enabling control logic
    always @ (posedge clk) begin
        if (reset) begin
            functional_out <= 8'b0;
        end else begin
            if (select) begin
                functional_out <= {4'b0, counter_out};
            end else begin
                functional_out <= {4'b0, converter_out};
            end
        end
    end

    // Assign the output signal
    assign q = functional_out;

endmodule
module binary_counter (
    input clk,
    input reset,
    output reg [3:0] count
);
    always @ (posedge clk) begin
        if (reset) begin
            count <= 4'b0;
        end else begin
            count <= count + 1;
        end
    end
endmodule
module signed_mag_to_twos_comp (
    input [3:0] signed_mag,
    output reg [3:0] twos_comp
);
    always @ (signed_mag) begin
        if (signed_mag[3]) begin
            twos_comp <= ~(signed_mag - 1);
        end else begin
            twos_comp <= signed_mag;
        end
    end
endmodule