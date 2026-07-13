module infrared_control_sva (
    input logic botao_1,
    input logic botao_2,
    input logic botao_3,
    input logic botao_4,
    input logic clk,
    input logic estado_atual,
    input logic estado_prox,
    input logic infrared,
    input logic led,
    input logic reset,
    input logic BOT14,
    input logic BOT23,
    input logic IDLE,
    input logic KEEP1,
    input logic KEEP2,
    input logic KEEP3,
    input logic KEEP4,
    input logic PRESS,
    input logic count
);

property ResetSynceotid; @(posedge clk) (reset) |-> (estado_atual == IDLE) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (infrared) |-> (led) ;endproperty
assert property (ResetSynceotid_2);

property ValidTriggereotid; @(posedge clk) (infrared) &&  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  ) |->  (  (count)  == (count + 1)  ) ;endproperty
assert property (ValidTriggereotid);

property ValidTriggereotid_2; @(posedge clk) (infrared) &&  (  (estado_atual == IDLE)  ) &&  (  (count)  != 130  ) |->  (  (estado_prox)  == (PRESS)  ) ;endproperty
assert property (ValidTriggereotid_2);

property ValidTriggereotid_3; @(posedge clk) (infrared) &&  (  (estado_atual == IDLE)  ) &&  (  (count)  == 130  ) &&  (  (infrared) == 1 ) |->  (  (estado_prox)  == (BOT14)  ) ;endproperty
assert property (ValidTriggereotid_3);

property ValidTriggereotid_4; @(posedge clk) (infrared) &&  (  (estado_atual == IDLE)  ) &&  (  (count)  == 130  ) &&  (  (infrared) != 1 ) |->  (  (estado_prox)  == (BOT23)  ) ;endproperty
assert property (ValidTriggereotid_4);

property ResetSynceotid_3; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  != 190  ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 1  ) ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 190  ) &&  (  (infrared) == 1 ) |->  (  (botao_1)  == 1  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 190  ) &&  (  (infrared) != 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 1  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  != 170  ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 170  ) &&  (  (infrared) == 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 1  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 170  ) &&  (  (infrared) != 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 1  ) ;endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  != 130  ) |->  (  (botao_1)  == 1  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 130  ) &&  (  (infrared) == 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(posedge clk) (  (infrared)  ||  (  (estado_atual == PRESS)  ||  (estado_atual == BOT14)  ||  (estado_atual == BOT23)  ||  (estado_atual == KEEP1)  ||  (estado_atual == KEEP2)  ||  (estado_atual == KEEP3)  ||  (estado_atual == KEEP4)  )  ) &&  (  (count)  == 130  ) &&  (  (infrared) != 1 ) |->  (  (botao_1)  == 0  &&  (botao_2)  == 0  &&  (botao_3)  == 0  &&  (botao_4)  == 0  ) ;endproperty
assert property (ResetSynceotid_11);

endmodule