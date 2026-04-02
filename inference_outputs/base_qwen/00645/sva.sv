module LedOutput_sva (
    input logic [8:0] key_input,
    output logic [4:0] led_output
);
    // Sequential logic driven by always @* block
    // No clock or reset signals present

    // Key signal driven by key_input
    // LED output driven by key_input

    // Behavior: LED output should match the binary representation of key_input
    // except for the default case which should not occur
    led_output_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn) (key_input inside {[0:127]}) |-> (led_output == {key_input[4:0], key_input[7:5], key_input[3:0]})
    );
endmodule