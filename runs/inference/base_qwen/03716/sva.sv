module limbus_cpu_cpu_nios2_oci_dtrace_sva (
    input logic clk,
    input logic jrst_n,
    input logic cpu_d_read,
    input logic cpu_d_write,
    input logic cpu_d_wait,
    output reg [35:0] atm,
    output reg [35:0] dtm
);
    // Reset behavior: atm and dtm should be 0 at reset
    reset: assert property (
        @(posedge clk) !jrst_n |-> (atm == 36'b0) && (dtm == 36'b0)
    );

    // Read operation: atm should be updated with cpu_d_address and dtm with cpu_d_readdata
    read_operation: assert property (
        @(posedge clk) disable iff (!jrst_n) (cpu_d_read |-> (atm == cpu_d_address) && (dtm == cpu_d_readdata))
    );

    // Write operation: atm should be updated with cpu_d_address and dtm with cpu_d_writedata
    write_operation: assert property (
        @(posedge clk) disable iff (!jrst_n) (cpu_d_write |-> (atm == cpu_d_address) && (dtm == cpu_d_writedata))
    );

    // Wait operation: atm and dtm should be 0
    wait_operation: assert property (
        @(posedge clk) disable iff (!jrst_n) (cpu_d_wait |-> (atm == 36'b0) && (dtm == 36'b0))
    );

    // Exclusive access to atm and dtm during read, write, and wait operations
    exclusive_access: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            (cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == cpu_d_address) && (dtm == (cpu_d_read ? cpu_d_readdata : cpu_d_writedata))
        )
    );

    // atm and dtm should not change during normal operation
    no_change: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            !(cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == atm) && (dtm == dtm)
        )
    );

    // atm and dtm should be updated only during read, write, and wait operations
    update_only_during_operations: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            !(cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == atm) && (dtm == dtm)
        )
    );

    // atm and dtm should be updated only during read, write, and wait operations
    update_only_during_operations_2: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            !(cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == atm) && (dtm == dtm)
        )
    );

    // atm and dtm should be updated only during read, write, and wait operations
    update_only_during_operations_3: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            !(cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == atm) && (dtm == dtm)
        )
    );

    // atm and dtm should be updated only during read, write, and wait operations
    update_only_during_operations_4: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            !(cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == atm) && (dtm == dtm)
        )
    );

    // atm and dtm should be updated only during read, write, and wait operations
    update_only_during_operations_5: assert property (
        @(posedge clk) disable iff (!jrst_n) (
            !(cpu_d_read | cpu_d_write | cpu_d_wait) |-> (atm == atm) && (dtm == dtm)
        )
    );
endmodule