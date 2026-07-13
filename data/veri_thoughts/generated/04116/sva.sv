module MIO_BUS_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] BTN,
    input logic [7:0] SW,
    input logic mem_w,
    input logic [31:0] Cpu_data2bus,
    input logic [31:0] addr_bus,
    input logic [31:0] ram_data_out,
    input logic [7:0] led_out,
    input logic [31:0] counter_out,
    input logic counter0_out,
    input logic counter1_out,
    input logic counter2_out,
    input logic [31:0] Cpu_data4bus,
    input logic [31:0] ram_data_in,
    input logic [9:0] ram_addr,
    input logic data_ram_we,
    input logic GPIOf0000000_we,
    input logic GPIOe0000000_we,
    input logic counter_we,
    input logic [31:0] Peripheral_in
);

    // GPIOe write enable is never asserted by this RTL.
    check_gpioe_always_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        GPIOe0000000_we == 1'b0
    );

    // Address region 0x0 selects RAM and forwards RAM read data.
    check_addr0_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        (addr_bus[31:28] == 4'h0) |-> (
            (data_ram_we == mem_w) &&
            (counter_we == 1'b0) &&
            (GPIOf0000000_we == 1'b0) &&
            (GPIOe0000000_we == 1'b0) &&
            (ram_addr == addr_bus[11:2]) &&
            (ram_data_in == Cpu_data2bus) &&
            (Peripheral_in == 32'h0) &&
            (Cpu_data4bus == ram_data_out)
        )
    );

    // Address region 0xE drives the GPIOf write enable and returns counter data.
    check_addre_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        (addr_bus[31:28] == 4'he) |-> (
            (data_ram_we == 1'b0) &&
            (counter_we == 1'b0) &&
            (GPIOf0000000_we == mem_w) &&
            (GPIOe0000000_we == 1'b0) &&
            (ram_addr == 10'h0) &&
            (ram_data_in == 32'h0) &&
            (Peripheral_in == Cpu_data2bus) &&
            (Cpu_data4bus == counter_out)
        )
    );

    // Address region 0xF with addr_bus[2]=1 selects counter write and counter readback.
    check_addrf_counter_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        ((addr_bus[31:28] == 4'hf) && addr_bus[2]) |-> (
            (data_ram_we == 1'b0) &&
            (counter_we == mem_w) &&
            (GPIOf0000000_we == 1'b0) &&
            (GPIOe0000000_we == 1'b0) &&
            (ram_addr == 10'h0) &&
            (ram_data_in == 32'h0) &&
            (Peripheral_in == Cpu_data2bus) &&
            (Cpu_data4bus == counter_out)
        )
    );

    // Address region 0xF with addr_bus[2]=0 selects GPIOf write and GPIO/status readback.
    check_addrf_gpio_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        ((addr_bus[31:28] == 4'hf) && !addr_bus[2]) |-> (
            (data_ram_we == 1'b0) &&
            (counter_we == 1'b0) &&
            (GPIOf0000000_we == mem_w) &&
            (GPIOe0000000_we == 1'b0) &&
            (ram_addr == 10'h0) &&
            (ram_data_in == 32'h0) &&
            (Peripheral_in == Cpu_data2bus) &&
            (Cpu_data4bus == {counter0_out, counter1_out, counter2_out, 9'h00, led_out, BTN, SW})
        )
    );

    // Unmapped address regions leave all outputs at their default zeros.
    check_default_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        ((addr_bus[31:28] != 4'h0) && (addr_bus[31:28] != 4'he) && (addr_bus[31:28] != 4'hf)) |-> (
            (data_ram_we == 1'b0) &&
            (counter_we == 1'b0) &&
            (GPIOf0000000_we == 1'b0) &&
            (GPIOe0000000_we == 1'b0) &&
            (ram_addr == 10'h0) &&
            (ram_data_in == 32'h0) &&
            (Peripheral_in == 32'h0) &&
            (Cpu_data4bus == 32'h0)
        )
    );

    // RAM write enable can only occur on the RAM decode with mem_w asserted.
    check_data_ram_we_qualification: assert property (
        @(posedge clk) disable iff (1'b0)
        data_ram_we |-> ((addr_bus[31:28] == 4'h0) && mem_w)
    );

    // Counter write enable can only occur on 0xF with addr_bus[2]=1 and mem_w asserted.
    check_counter_we_qualification: assert property (
        @(posedge clk) disable iff (1'b0)
        counter_we |-> ((addr_bus[31:28] == 4'hf) && addr_bus[2] && mem_w)
    );

    // GPIOf write enable can only occur on 0xE or 0xF with addr_bus[2]=0 and mem_w asserted.
    check_gpiof_we_qualification: assert property (
        @(posedge clk) disable iff (1'b0)
        GPIOf0000000_we |-> (((addr_bus[31:28] == 4'he) || ((addr_bus[31:28] == 4'hf) && !addr_bus[2])) && mem_w)
    );

    // The write enables are mutually exclusive.
    check_write_enable_mutex: assert property (
        @(posedge clk) disable iff (1'b0)
        !((data_ram_we && counter_we) ||
          (data_ram_we && GPIOf0000000_we) ||
          (data_ram_we && GPIOe0000000_we) ||
          (counter_we && GPIOf0000000_we) ||
          (counter_we && GPIOe0000000_we) ||
          (GPIOf0000000_we && GPIOe0000000_we))
    );

endmodule