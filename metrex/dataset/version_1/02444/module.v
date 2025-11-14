
module d_ff (
    input clk,
    input reset,
    input set,
    input enable,
    input test,
    input d,
    output reg q
);

    // Voltage supply signals
    supply1 vpwr;
    supply0 vgnd;

    // Internal signals
    wire test_mux_out;
    wire set_mux_out;
    wire inv_out;
    reg dff_in;

    // Test Mux
    assign test_mux_out = test ? d : 1'b0;

    // Set Mux
    assign set_mux_out = set ? 1'b1 : test_mux_out;

    // Inverter
    assign inv_out = ~set_mux_out;

    // D Flip-Flop
    always @(posedge clk, posedge reset) begin
        if (reset) begin
            dff_in <= 1'b0;
        end else if (enable) begin
            dff_in <= inv_out;
        end
    end

    // Output Register
    always @* begin
        q <= dff_in;
    end

endmodule
