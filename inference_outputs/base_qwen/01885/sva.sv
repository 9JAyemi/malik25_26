```systemverilog
module rominfr_sva (
    input logic clk,
    input logic en,
    input logic [4:0] addr,
    output logic [3:0] data
);
    // ROM data output is correct for the given address and enable
    rom_data_correct: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_en: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_addr: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_comb: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_default: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_case: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_always: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_case_default: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_case_always: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
    rom_data_correct_case_default_always: assert property (
        @(posedge clk) disable iff (!en) (data == 4'bXXXX)
    );
endmodule
```