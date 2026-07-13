property ClockSynceotid; @(posedge input_clk) (input_clk) |-> (clk_int) && (clk_io); endproperty 
 
 property SyncIneotid; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFG") |-> (clk_int) && (clk_io); endproperty 
 
 property SyncIneotid; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFR") |-> (clk_int) && (clk_io) && (output_clk); endproperty 
 
 property SyncIneotid; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFIO") |-> (clk_int) && (clk_io) && (output_clk); endproperty 
 
 property SyncIneotid; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFIO2") |-> (clk_int) && (clk_io) && (output_clk); endproperty 
 
 property SyncIneotid; @(posedge input_clk) (input_clk) |-> (output_q) == (input_d); endproperty 
 