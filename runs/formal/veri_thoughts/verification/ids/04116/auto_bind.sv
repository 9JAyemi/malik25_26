// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_gpioe_always_zero, assert, property, posedge, disable, iff, b0, check_addr0_decode, h0, check_addre_decode, he, check_addrf_counter_decode, hf, check_addrf_gpio_decode, h00, check_default_decode, check_data_ram_we_qualification, check_counter_we_qualification, check_gpiof_we_qualification, check_write_enable_mutex
bind MIO_BUS MIO_BUS_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .BTN(BTN),
    .SW(SW),
    .mem_w(mem_w),
    .Cpu_data2bus(Cpu_data2bus),
    .addr_bus(addr_bus),
    .ram_data_out(ram_data_out),
    .led_out(led_out),
    .counter_out(counter_out),
    .counter0_out(counter0_out),
    .counter1_out(counter1_out),
    .counter2_out(counter2_out),
    .Cpu_data4bus(Cpu_data4bus),
    .ram_data_in(ram_data_in),
    .ram_addr(ram_addr),
    .data_ram_we(data_ram_we),
    .GPIOf0000000_we(GPIOf0000000_we),
    .GPIOe0000000_we(GPIOe0000000_we),
    .counter_we(counter_we),
    .Peripheral_in(Peripheral_in)
);
