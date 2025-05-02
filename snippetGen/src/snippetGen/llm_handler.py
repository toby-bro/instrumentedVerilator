import getpass
import logging
import os
from typing import List, Literal, Optional

from langchain.chat_models import init_chat_model
from langchain_core.language_models.chat_models import BaseChatModel
from langchain_core.messages import BaseMessage, HumanMessage, SystemMessage

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

if 'MISTRAL_API_KEY' not in os.environ:
    os.environ['MISTRAL_API_KEY'] = getpass.getpass(prompt='Enter your Mistral API key: ')


class LLMHandler:
    """Handles initialization and interaction with different language models."""

    def __init__(self, model_type: Literal['openai', 'mistral', 'gemini']) -> None:
        """
        Initializes the LLMHandler with the specified model type.

        Args:
            model_type: The type of language model to use ('openai', 'mistral', 'gemini').

        Raises:
            ValueError: If the model type is unavailable or initialization fails.
        """
        self.llm: BaseChatModel = self._initialize_llm(model_type)
        logger.info(f'Using model: {self.llm.__class__.__name__}')

    def _initialize_llm(self, model_type: str) -> BaseChatModel:
        """Initializes and returns the language model instance using init_chat_model."""
        try:
            # Map model_type to provider and potentially model name
            if model_type == 'openai':
                # Ensure OPENAI_API_KEY is set in environment
                # init_chat_model defaults to gpt-3.5-turbo for openai if model isn't specified
                model_instance = init_chat_model(provider='openai', model='gpt-3.5-turbo')
            elif model_type == 'mistral':
                # Ensure MISTRAL_API_KEY is set in environment
                model_instance = init_chat_model(model='mistral-large-latest')
            elif model_type == 'gemini':
                # Ensure GOOGLE_API_KEY is set in environment
                model_instance = init_chat_model(provider='google_genai', model='gemini-pro')
            else:
                raise ValueError(f'Unsupported model type for init_chat_model: {model_type}')

            if model_instance is None:
                # This case might be less likely with init_chat_model if provider is valid
                raise ValueError(
                    f"Failed to initialize model for provider '{model_type}'. Check API keys and package installations.",  # noqa: E501
                )

            return model_instance

        except Exception as e:
            logger.error(f"Error initializing model type '{model_type}' using init_chat_model: {e}")
            logger.error('Check if the required package is installed and the corresponding API key is set.')
            raise ValueError(f'Failed to initialize LLM: {e}') from e

    def invoke_llm(self, prompt: str, system_message: Optional[str] = None) -> str:
        """
        Invokes the initialized language model with the given prompt.

        Args:
            prompt: The main user prompt for the LLM.
            system_message: An optional system message to guide the LLM's behavior.

        Returns:
            The content of the LLM's response as a string.

        Raises:
            RuntimeError: If the LLM invocation fails.
        """
        messages: List[BaseMessage] = []
        if system_message:
            messages.append(SystemMessage(content=system_message))
        messages.append(HumanMessage(content=prompt))

        try:
            logger.info('Invoking LLM...')
            response = self.llm.invoke(messages)
            logger.info('LLM invocation complete.')
            if isinstance(response.content, str):
                # Basic cleaning: remove markdown code block fences if present
                content = response.content.strip()
                # Handle various markdown formats for code blocks
                if content.startswith('```verilog'):
                    content = content[len('```verilog') :].strip()
                elif content.startswith('```vhdl'):  # Handle other potential languages just in case
                    content = content[len('```vhdl') :].strip()
                elif content.startswith('```c'):
                    content = content[len('```c') :].strip()
                elif content.startswith('```'):
                    content = content[len('```') :].strip()

                if content.endswith('```'):
                    content = content[: -len('```')].strip()
                return content
            # Handle potential non-string content if necessary
            logger.warning('LLM response content is not a plain string.')
            return str(response.content)
        except Exception as e:
            logger.error(f'An error occurred during LLM invocation: {e}')
            raise RuntimeError('LLM invocation failed') from e
