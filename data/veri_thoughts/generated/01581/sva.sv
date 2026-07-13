module sensor_interface_sva (
    // Sampling clock/reset for SVA only; RTL has no clock or reset (purely combinational).
    input  logic                      CLK,
    input  logic                      RESETn,

    // DUT ports as observed inputs
    input  logic signed [15:0]        temperature,
    input  logic        [15:0]        pressure,
    input  logic        [7:0]         humidity,
    input  logic signed [15:0]        temp_out,
    input  logic        [15:0]        press_out,
    input  logic        [7:0]         hum_out
);

    // Temperature conversion matches: temp_out = temperature * 9 / 5 + 32 (signed arithmetic).
    check_temp_fahrenheit_conversion: assert property (
        @(posedge CLK) disable iff (!RESETn)
            temp_out == (temperature * 9 / 5 + 32)
    );

    // Pressure is passed through unchanged.
    check_pressure_passthrough: assert property (
        @(posedge CLK) disable iff (!RESETn)
            press_out == pressure
    );

    // Humidity is passed through unchanged.
    check_humidity_passthrough: assert property (
        @(posedge CLK) disable iff (!RESETn)
            hum_out == humidity
    );

endmodule